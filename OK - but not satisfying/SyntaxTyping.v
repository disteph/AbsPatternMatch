Require Import ssreflect List.

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


(* Tree Squeleton *)

Inductive sTree :=
| sleafP : sTree
| sleafN : sTree
| sdummy : sTree
| snode : sTree -> sTree -> sTree
| sqnode : sTree -> sTree.


(* Generic tree type, with two kinds of leaves A and B *)

Inductive Tree {C:Type}{A B: list C -> Type}: sTree -> list C -> Type  :=
| leafP : forall l, A l -> Tree sleafP l
| leafN : forall l, B l -> Tree sleafN l
| dummy : forall l, Tree sdummy l
| node  : forall l s1 s2, Tree s1 l -> Tree s2 l -> Tree (snode s1 s2) l
| qnode : forall l s so, Tree s (so::l) -> Tree (sqnode s) l.

Arguments leafP {C A B l} _ .
Arguments leafN {C A B l} _ .
Arguments dummy {C A B l} .
Arguments node {C A B l s1 s2} _ _ .
Arguments qnode {C A B l s} _ _ .




(* Lifting two relations RelP and RelN, respectively between A and C
and between B and D, into a relation between Trees A B and Trees C D
 *)

Definition Treelift {E F:Type} {A B: list E -> Type} {C D: list F -> Type}
           (RelQ:E -> F -> Prop)
           (RelP: forall l, A l ->  forall l', C l' -> Prop)
           (RelN: forall l, B l -> forall l', D l' -> Prop)
           {st} 
: forall l, @Tree E A B st l -> forall l', @Tree F C D st l' -> Prop.
Proof.
  induction st; move => l v l' Delta ; inversion v ; inversion Delta.
  exact (RelP l X l' X0).
  exact (RelN l X l' X0).
  exact True.
  exact ((IHst1 l X l' X1)/\(IHst2 l X0 l' X2)).
  exact ((RelQ so so0)/\(IHst _ X _ X0)).
Defined.

Record World :=
  {
    PVar:Type;
    NVar:Type;
    QVar:Type
  }
.

  (* Axiomatic specification for the implementation of contexts:
contexts map positive and negative variables to elements of A and B,
respectively.  These can be typing contexts (variables are mapped to
formula variables and molecules), or substitutions (variables are
mapped to positive and negative terms).

readp and readn are for reading the values
extends is the way to extend a context, thanks to a AB-@Tree.
corr is a property required of extensions:
if rho and Gamma are "RelP-RelN-related" (the values to which a variable is
mapped by rho and Gamma are RelP/RelN-related), and v and Delta are
"RelP-RelN-related" (as @Trees), then the extension of rho by v and the
extension of Gamma by Delta are "RelP-RelN-related".
   *)

Record ContType {C A B w} :=
  {
    readq : w.(QVar) -> C;
    readp : w.(PVar) -> A;
    readn : w.(NVar) -> B
  }.

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

Record AsSortable := 
  {
    astype:> Type
  }.

Definition AsTypable (C:AsSortable) :=  forall w:Type, list C -> Type.

(* Record AsTypable (C:AsSortable) :=  *)
(*   { *)
(*     asfun:> forall w:Type, list C -> Type *)
(*   }. *)

Definition DType {C} {A B: AsTypable C} {w}
  := @ContType C (A w.(QVar) nil) (B w.(QVar) nil) w.

Record ContextType := 
  {
    wextends: sTree -> World -> World;

    extends {C}{A B : AsTypable C} {w:World} {st}: 
      forall v : @Tree C (A w.(QVar)) (B w.(QVar)) st nil,
        @DType C A B w -> @DType C A B (wextends st w);

    corr {E F} {A B: AsTypable E}{C D: AsTypable F} {w:World} {st} : 
      forall (RelQ: E -> F -> Prop)
        (RelP: forall qVar,(qVar -> E)->(qVar -> F)-> forall l, A qVar l -> forall l', C qVar l' -> Prop)
        (RelN: forall qVar,(qVar -> E)->(qVar -> F)-> forall l, B qVar l -> forall l', D qVar l' -> Prop)
        (rho:@DType E A B w)
        (Gamma:@DType F C D w)
        v Delta,
        Treelift RelQ 
                 (RelP w.(QVar) rho.(readq) Gamma.(readq))
                 (RelN w.(QVar) rho.(readq) Gamma.(readq))
                 (st:=st) nil v nil Delta
        -> Contlift RelQ
                   (fun a b => RelP w.(QVar) rho.(readq) Gamma.(readq) nil a nil b)
                   (fun a b => RelN w.(QVar) rho.(readq) Gamma.(readq) nil a nil b)
                   rho Gamma
        ->  let w' := wextends st w in 
           let rho' := extends v rho in 
           let Gamma' := extends Delta Gamma in 
           Contlift RelQ
                    (fun a b => RelP w'.(QVar) rho'.(readq) Gamma'.(readq) nil a nil b)
                    (fun a b => RelN w'.(QVar) rho'.(readq) Gamma'.(readq) nil a nil b)
                    rho' Gamma'
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
Variable Term : Type -> Type.

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

Variable Sorts : AsSortable.
Variable SortingRel : forall {QVar}, (QVar -> Sorts) -> Term QVar -> Sorts -> Prop.


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

Inductive TermList {QVar} (Sigma:QVar -> Sorts): list Sorts -> Type := 
| TermNil : TermList Sigma nil
| TermCons: forall r s, SortingRel Sigma r s -> forall l, TermList Sigma l -> TermList Sigma (s::l).

Arguments TermNil {QVar Sigma}.
Arguments TermCons {QVar Sigma} r {s} _ {l} _ .

Fixpoint fset (A:Type) (l:list Type) : Type
  := match l with
      | nil => A
      | cons s l' => s -> fset A l'
    end.


Definition TermFamily (A:Type -> Type) :=
 fun (qVar:Type) (l:list Sorts) => fset (A qVar) (map (fun _ => Term qVar) l)
.

(* Definition TermFamily (A:Type -> Type) := *)
(* {|  *)
(*   asfun := fun (qVar:Type) (l:list Sorts) => fset (A qVar) (map (fun _ => Term qVar) l) *)
(* |}. *)


Definition TypeTree qVar := @Tree Sorts (TermFamily Atom qVar) (TermFamily Molecule qVar).

Fixpoint substTermsP {A qVar l l' Sigma} (tl:@TermList qVar Sigma l)
  := match tl in @TermList _ _ x 
          return TermFamily A qVar (app x l') -> TermFamily A qVar l' with
      | TermNil => fun a => a
      | TermCons r s proof l' tl' => fun a => substTermsP tl' (a r)
    end.

Fixpoint cast {A qVar l} : TermFamily A qVar l -> TermFamily A qVar (app l nil)
  := match l as x
          return TermFamily A qVar x  -> TermFamily A qVar (app x nil) with
      | nil => fun a => a
      | cons so l' => fun a => fun o => cast (a o)
    end.

Definition substTerms {A qVar l Sigma} tl X := @substTermsP A qVar l nil Sigma tl (cast X).


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

Definition TContext w := @DType Sorts 
                               (TermFamily Atom)
                               (TermFamily Molecule)
                               w.

Definition Textends {w st} Delta Gamma 
  := Context.(@extends) Sorts
                       (TermFamily Atom) 
                       (TermFamily Molecule)
                       w st Delta Gamma
.


(* Here is the typing system *)

Inductive TypingPos {w} (Gamma: TContext w) : @Pos w -> Molecule w.(QVar) -> Prop :=
| typingpos: forall p v Delta A,
               (PatternsTyped p Delta A)
               -> TypingSub Gamma _ v Delta TermNil 
               -> TypingPos Gamma (pos p v) A
                           
with TypingSub {w} (Gamma: TContext w)
     : forall l {st}, @TermTree w st -> TypeTree w.(QVar) st l -> TermList Gamma.(readq) l -> Prop :=
     | typingsub_leafl: forall l xp x tl,
                          substTerms tl x = Gamma.(readp) xp
                          -> TypingSub Gamma l (tleafP xp) (leafP x) tl
     | typingsub_leafr: forall l nt A l',
                          TypingNeg Gamma nt (substTerms l' A) ->
                          TypingSub Gamma l (tleafN nt) (leafN A) l'
     | typingsub_dummy: forall l l',
                          TypingSub Gamma l tdummy dummy l'
     | typingsub_node: forall l s1 s2 (v1:TermTree s1) (v2:TermTree s2)
                         Delta1 Delta2 l',
                         TypingSub Gamma _ v1 Delta1 l'
                         -> TypingSub Gamma _ v2 Delta2 l'
                         -> TypingSub Gamma l (tnode v1 v2) (node Delta1 Delta2) l'
     | typingsub_qnode: forall l s (v:TermTree s) so Delta r l' proof,
                          TypingSub Gamma _ v Delta (TermCons r proof l')
                          -> TypingSub Gamma l (tqnode r v) (qnode so Delta) l'

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