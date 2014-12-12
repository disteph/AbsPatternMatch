Require Import ssreflect List .

(* 
Realisability models for a Zeilberger-style system.

The system is a proof-term assignment system for an abstract focused
sequent calculus for a logic made of synthetic connectives that are
abstracted away.

We formalise proof-terms and typing, and define a generic
realisability model for such proof-terms, in the style of Munch (based
on orthogonality). We prove the Adequacy lemma.

Note: In Zeilberger's style, proving a negative formula can be done
with an inference rule involving a higher-order premise.
Correspondingly, inhabiting a negative formula can be done by reifying
a meta-level function into the proof-term language.

 *)


(*********)
(* Trees *)
(*********)

(* Tree Squeleton *)

Inductive sTree :=
| sleafP : sTree
| sleafN : sTree
| sdummy : sTree
| snode : sTree -> sTree -> sTree
| sqnode : sTree -> sTree.


(* Generic tree type, with two kinds of leaves A and B *)

Inductive Tree {C A B: Type}: sTree -> Type  :=
| leafP : A -> Tree sleafP
| leafN : B -> Tree sleafN
| dummy : Tree sdummy
| node  : forall s1 s2, Tree s1 -> Tree s2 -> Tree (snode s1 s2)
| qnode : forall s, C -> Tree s -> Tree (sqnode s).

Arguments leafP {C A B} _ .
Arguments leafN {C A B} _ .
Arguments dummy {C A B} .
Arguments node {C A B s1 s2} _ _ .
Arguments qnode {C A B s} _ _ .




(* Lifting three relations RelQ, RelP and RelN, respectively between E
and F, between A and C and between B and D, into a relation between
Trees E A B and Trees F C D *)

Definition Treelift {E F A B C D: Type}
           (RelQ: E -> F -> Prop)
           (RelP: A -> C -> Prop)
           (RelN: B -> D -> Prop)
           {st} 
: @Tree E A B st -> @Tree F C D st -> Prop.
Proof.
  induction st; move => v Delta ; inversion v ; inversion Delta.
  exact (RelP X X0).
  exact (RelN X X0).
  exact True.
  exact ((IHst1 X X1)/\(IHst2 X0 X2)).
  exact ((RelQ X X1)/\(IHst X0 X2)).
Defined.


(************)
(* Contexts *)
(************)

(* Axiomatic specification for the implementation of contexts:

Contexts can be typing contexts (variables are mapped to "types"), or
substitutions (variables are mapped to "terms").

Contexts map quantifiable, positive and negative variables to elements
of C, A and B, respectively.
readq, readp and readn are for reading the values.
 *)


Record World :=
  {
    PVar:Type;
    NVar:Type;
    QVar:Type
  }
.

Record ContType {C A B w} :=
  {
    readq : w.(QVar) -> C;
    readp : w.(PVar) -> A;
    readn : w.(NVar) -> B
  }.

Definition Contmap {E F A B C D:Type}
           (fQ: E -> F)
           (fP: A -> C) 
           (fN: B -> D)
           {w} 
: @ContType E A B w -> @ContType F C D w
  := fun Gamma => 
      {| readq := fun xq => fQ (Gamma.(readq) xq);
         readp := fun xp => fP (Gamma.(readp) xp);
         readn := fun xn => fN (Gamma.(readn) xn)
      |}
.

Definition Contlift {E F A B C D:Type}
           (RelQ: E -> F -> Prop)
           (RelP: A -> C -> Prop) 
           (RelN: B -> D -> Prop)
           {w} 
: @ContType E A B w -> @ContType F C D w -> Prop
  := fun Gamma rho =>
        (forall xq, RelQ (Gamma.(readq) xq) (rho.(readq) xq))
        /\ (forall xp, RelP (Gamma.(readp) xp) (rho.(readp) xp))
        /\ (forall xn, RelN (Gamma.(readn) xn) (rho.(readn) xn))
.

(* In ContextType, we have an implementation of operations about
contexts:

- extends is the way to extend a context, thanks to a CAB-@Tree.

- corr is a property required of extensions:

if rho and Gamma are "RelP-RelN-related" (the values to which a variable is
mapped by rho and Gamma are RelP/RelN-related), and v and Delta are
"RelP-RelN-related" (as @Trees), then the extension of rho by v and the
extension of Gamma by Delta are "RelP-RelN-related".

*)


Definition correctNaming {E A B C D:Type} {qVar st} (Sigma: qVar -> E) v nametree
  := Treelift (st:=st) (A:=A) (B:=B) (C:=C) (D:=D)
             (fun s q => Sigma q = s)
             (fun _ _ => True)
             (fun _ _ => True)
             v nametree.

Record ContextType := 
  {
    wextends: sTree -> World -> World;
    qinject st w : w.(QVar) -> (wextends st w).(QVar);
    qnew    st w : @Tree (wextends st w).(QVar) unit unit st;

    extends {C A B : Type} {w:World} {st}: 
      forall v : @Tree C A B st, @ContType C A B w -> @ContType C A B (wextends st w);

    qnewwt {C A B : Type} {w:World} {st}:
      forall (v: @Tree C A B st) rho, correctNaming (extends v rho).(readq) v (qnew st w);

    corr {E F A B C D: Type} {w:World} {st} : 
      forall (RelQ: E -> F -> Prop)
        (RelP: A -> C -> Prop)
        (RelN: B -> D -> Prop)
        (rho:@ContType E A B w)
        (Gamma:@ContType F C D w)
        v Delta,
        Treelift RelQ RelP RelN (st:=st) v Delta
        -> Contlift RelQ RelP RelN rho Gamma
        -> Contlift RelQ RelP RelN (extends v rho) (extends Delta Gamma)
  }
.


(* We assume we have an implementation of contexts *)

Variable Context: ContextType.

(***************)
(* PROOF-TERMS *)
(***************)

(* The language of proof-terms is parameterised by:
- Patterns: type of elements that can be thought as patterns
To each pattern p is associated a tree skeleton PatTree p
- Term: type of witnesses (the objects that the logic quantifies over)
- a world w specifying the variables to which the proof-term can refer
 *)

Variable Patterns : Type.
Variable PatTree: Patterns -> sTree.

Record TermAlgebra :=
  {
    TermSet :> Type -> Type;
    varTerm {qVar} : qVar -> TermSet qVar 
  }
.

Variable Term : TermAlgebra.

(* The language of proof-terms has 5 syntactic categories:
- commands 
(negative term+positive term)
- negative terms 
(reification of a meta-level partial function from patterns to commands,
represented as a total function to option commands)
- positive terms 
(pattern + prof-term tree)
- proof-term trees 
("a way to fill the pattern's holes")
- option commands
(the result of a partial function to commands)
*)

Inductive Pos {w}:Type :=
| pos: forall p:Patterns, @TermTree w (PatTree p) -> Pos
with TermTree {w}: sTree -> Type :=
     | tleafP: w.(PVar) -> TermTree sleafP
     | tleafN: (@Neg w) -> TermTree sleafN
     | tdummy: TermTree sdummy
     | tnode s1 s2: @TermTree w s1 -> @TermTree w s2 -> TermTree (snode s1 s2)
     | tqnode s: Term w.(QVar) -> @TermTree w s -> TermTree (sqnode s)
with Neg {w}:Type :=
     | rei : (forall p:Patterns, @OptionCommand (Context.(wextends) (PatTree p) w)) -> Neg
with OptionCommand {w}: Type :=
     | some: @Command w -> OptionCommand
     | none
with Command {w}: Type := 
     | cut   : Neg  -> Pos -> Command
     | select: w.(NVar) -> Pos -> Command.

Arguments tnode {w s1 s2} _ _ .
Arguments tqnode {w s} _ _ .


Scheme pos_ind :=
  Induction for Pos Sort Prop
  with termtree_ind :=
  Induction for TermTree Sort Prop
  with neg_ind :=
    Induction for Neg Sort Prop
    with ocommand_ind :=
      Induction for OptionCommand Sort Prop
      with command_ind :=
        Induction for Command Sort Prop.

Combined Scheme term_ind from pos_ind, termtree_ind, neg_ind, ocommand_ind, command_ind.


(*****************)
(* Abbreviations *)
(*****************)

Definition Reifiable {w} := forall p:Patterns, @OptionCommand (Context.(wextends) (PatTree p) w).

Notation "x + y" := (sum x y).
Definition NegVar w := @Neg w + w.(NVar).

Notation "x £ y" := (prod x y) (at level 80, right associativity) : type_scope.

Inductive cexists_as {w} : @OptionCommand w -> @Command w -> Prop :=
  cnotnone: forall o, cexists_as (some o) o
.

Notation "x =cis= y" := (cexists_as x y) (at level 30, right associativity).

Lemma somecis {w} {u} {c: @Command w} : u =cis= c -> u = some c.
Proof.
    by elim.
Qed.



(*********)
(* TYPES *)
(*********)

(* The language of types is given by 
- Sorts:    sorts for terms
- Atom:     type of atoms
- Molecule: type of molecules *)

Variable Sorts : Type.
Variable SortingRel: forall {QVar}, (QVar -> Sorts) -> Term QVar -> Sorts -> Prop.
Variable SortedVar: forall {QVar} Sigma (xq:QVar), SortingRel Sigma (Term.(varTerm) xq) (Sigma xq). 

Record QRenamable :=
  { QRenamablesupport :> Type -> Type;
    qrename {QVar1 QVar2}
    : (QVar1 -> QVar2) -> (QRenamablesupport QVar1 -> QRenamablesupport QVar2)
  }.

Variable Atom Molecule: QRenamable.



(************************************)
(* Parameterised types              *)
(* Types are parameterised by terms *)
(************************************)

Inductive TermList {QVar} (P: Term QVar -> Sorts -> Prop): list Sorts -> Type :=
| TermNil : TermList P nil
| TermCons: forall r s, P r s -> forall l, TermList P l -> TermList P (s::l).

Arguments TermNil {QVar P}.
Arguments TermCons {QVar P} r {s} _ {l} _ .

Definition TTermList {QVar} (Sigma:QVar -> Sorts): list Sorts -> Type :=
  TermList (SortingRel Sigma).

Definition UTTermList {QVar} : list Sorts -> Type :=
  @TermList QVar (fun _ _ => True).

Fixpoint TermListMap {QVar Sigma l} (tl:@TTermList QVar Sigma l): UTTermList l :=
  match tl with
      | TermNil => TermNil
      | TermCons r _ _ _ tl' => TermCons r (Logic.I) (TermListMap tl')
end.

Fixpoint fset (A:Type) (l:list Type) : Type
  := match l with
      | nil => A
      | cons s l' => s -> fset A l'
    end.

Definition Family_base (A:QRenamable) (qVar:Type) (l:list Sorts)
  := fset (A qVar) (map (fun _ => Term qVar) l).

Definition Family (A:QRenamable) (qVar:Type) (l:list Sorts)
  := forall qVar' (qi: qVar -> qVar'), Family_base A qVar' l.

Fixpoint substTerms_base {A qVar P l} (tl:@TermList qVar P l)
  := match tl in @TermList _ _ x
          return Family_base A qVar x -> A qVar with
      | TermNil => fun a => a
      | TermCons r s proof l' tl' => fun a => substTerms_base tl' (a r)
    end.

Definition substTermsNU {A qVar qVar' l P} 
           (qi: qVar -> qVar')
           (tl:@TermList qVar' P l)
           (X: Family A qVar l)
  := substTerms_base tl (X qVar' qi).

Definition substTerms {A qVar l P} := @substTermsNU A qVar qVar l P (fun i => i).

Inductive TypeTree qVar: sTree -> list Sorts -> Type  :=
| TleafP : forall l, Family Atom qVar l -> TypeTree qVar sleafP l
| TleafN : forall l, Family Molecule qVar l -> TypeTree qVar sleafN l
| Tdummy : forall l, TypeTree qVar sdummy l
| Tnode  : forall l s1 s2, TypeTree qVar s1 l -> TypeTree qVar s2 l -> TypeTree qVar (snode s1 s2) l
| Tqnode : forall l s so, TypeTree qVar s (so::l) -> TypeTree qVar (sqnode s) l.

Arguments TleafP {qVar l} _.
Arguments TleafN {qVar l} _.
Arguments Tdummy {qVar l}.
Arguments Tnode {qVar l s1 s2} _ _.
Arguments Tqnode {qVar l s} _ _.

Definition namedTypeTree {st qVar qVar'} (qi: qVar -> qVar') 
           (ls: list Sorts) (lq: @UTTermList qVar' ls)
           (Delta:TypeTree qVar st ls) (qn : @Tree qVar' unit unit st)
: @Tree Sorts (Atom qVar') (Molecule qVar') st.
Proof.
  move:ls lq Delta.
  induction st => ls lq Delta; inversion Delta; inversion qn => //=.
  exact (leafP(substTermsNU qi lq X)).
  exact (leafN(substTermsNU qi lq X)).
  exact (dummy).
  exact (node (IHst1 X1 ls lq X) (IHst2 X2 ls lq X0)).
  exact (qnode so (IHst X1 (so::ls) (TermCons (Term.(varTerm) X0) (Logic.I) lq) X)).
Defined.

(**********)
(* TYPING *)
(**********)

(* This is the parameter that integrates the logical connectives.
It is a relation expressing:
"A formula can be decomposed into a TypeTree according to a pattern."
Example:
(A\/(B/\C)) can be decomposed into B,C according to the pattern inj2(_,_)
 *)
Variable PatternsTyped 
: forall (p:Patterns) {qVar}, TypeTree qVar (PatTree p) nil -> Molecule qVar -> Prop.


(* A typing context maps positive variables atoms and negative variables to molecules *)

Definition TContext w := @ContType Sorts 
                                  (Atom w.(QVar))
                                  (Molecule w.(QVar))
                                  w.

Definition Textends {w st} Delta Gamma 
  :=  let newGam := Contmap (w:=w)
                    (fun i => i)
                    (Atom.(qrename) (Context.(qinject) st w))
                    (Molecule.(qrename) (Context.(qinject) st w))
                    Gamma
     in
     Context.(extends) (namedTypeTree (Context.(qinject) st w) nil TermNil Delta
                                      (Context.(qnew) st w)
                       )
                       newGam
.


(* Here is the typing system *)

Inductive TypingPos {w} (Gamma: TContext w) : @Pos w -> Molecule w.(QVar) -> Prop :=
| typingpos: forall p v Delta A,
               (PatternsTyped p Delta A)
               -> TypingSub Gamma _ v Delta TermNil 
               -> TypingPos Gamma (pos p v) A
                           
with TypingSub {w} (Gamma: TContext w)
     : forall l {st}, @TermTree w st -> TypeTree w.(QVar) st l -> TTermList Gamma.(readq) l -> Prop :=
     | typingsub_leafl: forall l xp x tl,
                          substTerms tl x = Gamma.(readp) xp
                          -> TypingSub Gamma l (tleafP xp) (TleafP x) tl
     | typingsub_leafr: forall l nt A l',
                          TypingNeg Gamma nt (substTerms l' A) ->
                          TypingSub Gamma l (tleafN nt) (TleafN A) l'
     | typingsub_dummy: forall l l',
                          TypingSub Gamma l tdummy Tdummy l'
     | typingsub_node: forall l s1 s2 (v1:TermTree s1) (v2:TermTree s2)
                         Delta1 Delta2 l',
                         TypingSub Gamma _ v1 Delta1 l'
                         -> TypingSub Gamma _ v2 Delta2 l'
                         -> TypingSub Gamma l (tnode v1 v2) (Tnode Delta1 Delta2) l'
     | typingsub_qnode: forall l s (v:TermTree s) so Delta r l' proof,
                          TypingSub Gamma _ v Delta (TermCons r proof l')
                          -> TypingSub Gamma l (tqnode r v) (Tqnode so Delta) l'

with TypingNeg {w} (Gamma: TContext w): @Neg w -> Molecule w.(QVar) -> Prop :=
     | typingneg: forall f A,
                    (forall p c, (f p) =cis= c -> exists Delta, PatternsTyped p Delta A)
                    ->
                    (forall p Delta, (PatternsTyped p Delta A)
                            -> @TypingOptionCommand 
                                (Context.(wextends) (PatTree p) w)
                                (Textends Delta Gamma) 
                                (f p))
                    -> TypingNeg Gamma (rei f) A  

with TypingOptionCommand {w} (Gamma: TContext w): @OptionCommand w -> Prop :=
     | typingoption: forall c,
                       TypingCommand Gamma c
                       -> TypingOptionCommand Gamma (some c)

with TypingCommand {w} (Gamma: TContext w): @Command w -> Prop :=
     | typingcut: forall nt pt A,
                    TypingNeg Gamma nt A
                    -> TypingPos Gamma pt A
                    -> TypingCommand Gamma (cut nt pt)
     | typingselect: forall xn pt,
                       TypingPos Gamma pt (Gamma.(readn) xn)
                       -> TypingCommand Gamma (select xn pt)
.

(* We create the induction principle on typing trees *)

Arguments TypingSub {w} Gamma {l st} _ _ _ .

Scheme typingPos_ind := 
  Induction for TypingPos Sort Prop
  with typingSub_ind := 
  Induction for TypingSub Sort Prop
  with typingNeg_ind := 
    Induction for TypingNeg Sort Prop
    with typingOptionCommand_ind := 
      Induction for TypingOptionCommand Sort Prop
      with typingCommand_ind := Induction for TypingCommand Sort Prop
.

Combined Scheme typing_ind from typingPos_ind, typingSub_ind, typingNeg_ind, typingOptionCommand_ind, typingCommand_ind.

Print Assumptions typing_ind.