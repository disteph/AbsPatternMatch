Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
(* Unset Printing Implicit Defensive. *)
Open Scope type_scope.
Generalizable All Variables.

Require Import ssreflect List Basic.

Section QuantifyingStructure.
  (*************************)
  (* Quantifying Structure *)
  (*************************)

  Class QuantifyingStructures 
        (Sorts QWorld: Type) (Terms SoContexts: QWorld -> Type) 
        {SortingRel: forall {qLab}, SoContexts qLab -> Terms qLab -> Sorts -> Prop}
    := {QWorld := QWorld; Sorts := Sorts; 
       Terms := Terms; SoContexts := SoContexts; 
       SortingRel := @SortingRel}.

  Definition comp {A B C} (g:B -> C) (f:A -> B) x := g(f x).

  Class QuantifyingStructureswE
         `(QS:QuantifyingStructures (Sorts := So)
                                    (QWorld := Type)
                                    (SoContexts := fun qLab => qLab -> So))
        (asT : forall {qLab}, qLab -> Terms qLab)
        (lift2Terms: forall {qLab qLab'}, (qLab -> qLab') -> Terms qLab -> Terms qLab')
        (qLabSorting: 
          forall {qLab} Sigma (xq:qLab) s, SortingRel Sigma (asT xq) s <-> s = Sigma xq)
        (renSorting: forall {qLab qLab'} (pi:qLab -> qLab') (Sigma : SoContexts qLab') (r: Terms qLab) s, 
            SortingRel (QuantifyingStructures := QS) (comp Sigma pi) r s
            -> SortingRel Sigma (lift2Terms pi r) s)
    := { asT := @asT; lift2Terms := @lift2Terms; qLabSorting := @qLabSorting; renSorting := @renSorting }.

  (* We now assume we have a quantifying structure *)

  Context `(QS:QuantifyingStructures).

  (**************************************)
  (* Useful definitions for types       *)
  (* (types are parameterised by terms) *)
  (**************************************)

  Inductive AList A : list Sorts -> Type :=
  | TermNil   : AList A nil
  | TermCons s: A -> forall l, AList A l -> AList A (s::l).

  Definition TList (qLab:QWorld) := AList (Terms qLab).

  Definition DPair A := {l: list Sorts & A l}.

  Definition ex1 A (a:DPair A) := 
    match a with
      | existS l _ => l
    end.

  Definition ex2 A (a:DPair A): A (ex1 a) := 
    match a with
      | existS _ araw => araw
    end.

  Definition Inst A (qLab:QWorld) := DPair (fun l => A l * TList qLab l).

  Definition getA     A qLab (a:Inst A qLab) := let (b,_) := ex2 a in b.
  Definition getTerms A qLab (a:Inst A qLab) := let (_,b) := ex2 a in b.

End QuantifyingStructure.

Notation "[ x , y ]" := (existS (fun l => _ l * TList _ l) _ (x,y)).

(*****************)
(* Decomposition *)
(*****************)

(* Dec Squeleton *)

Inductive DecStruct :=
| sleafP : DecStruct
| sleafN : DecStruct
| sdummy : DecStruct
| snode : DecStruct -> DecStruct -> DecStruct
| sqnode : DecStruct -> DecStruct.

(* Generic Decomposition type, with two kinds of leaves A and B *)

Inductive Dec {C A B: Type}: DecStruct -> Type  :=
| leafP : A -> Dec sleafP
| leafN : B -> Dec sleafN
| dummy : Dec sdummy
| node  : forall {s1 s2}, Dec s1 -> Dec s2 -> Dec (snode s1 s2)
| qnode : forall {s}, C -> Dec s -> Dec (sqnode s).


(* Lifting three relations RelQ, RelP and RelN, respectively between E
and F, between A and C and between B and D, into a relation between
Decs E A B and Decs F C D *)

Definition Declift (E F A B C D: Type)
           (RelQ: E -> F -> Prop)
           (RelP: A -> C -> Prop)
           (RelN: B -> D -> Prop)
           {st} 
: @Dec E A B st -> @Dec F C D st -> Prop.
Proof.
  induction st; move => v Delta ; inversion v ; inversion Delta.
  exact (RelP X X0).
  exact (RelN X X0).
  exact True.
  exact ((IHst1 X X1)/\(IHst2 X0 X2)).
  exact ((RelQ X X1)/\(IHst X0 X2)).
Defined.

Section LAF.

  (*********)
  (* TYPES *)
  (*********)

  (* The language of types is given by 
- Sorts:    sorts for terms
- Atom:     type of atoms
- Molecule: type of molecules *)

  Class QSTypes
         `(QS:QuantifyingStructures)
         (Atom : list Sorts -> Type)
         (Molecule : list Sorts -> Type)
         (is_eq : forall {qLab:QWorld}, (Inst Atom qLab) -> (Inst Atom qLab) -> Prop)
    := {Atom := Atom; Molecule := Molecule; is_eq := @is_eq}.

  Inductive TypingDec `{QST:QSTypes}
  : DecStruct -> list Sorts -> Type  :=
  | TleafP : forall {l}, Atom l -> TypingDec sleafP l
  | TleafN : forall {l}, Molecule l -> TypingDec sleafN l
  | Tdummy : forall {l}, TypingDec sdummy l
  | Tnode  : forall {l s1 s2}, TypingDec s1 l -> TypingDec s2 l -> TypingDec (snode s1 s2) l
  | Tqnode : forall {l s} so, TypingDec s (so::l) -> TypingDec (sqnode s) l.

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

  Record World `{QS:QuantifyingStructures} :=
    {
      PLab:Type;
      NLab:Type;
      QLab:QWorld
    }.

  (* A typing context maps positive variables atoms and negative variables to molecules *)

  Record TypingContexts  `{QST:QSTypes} (wextends: DecStruct -> World -> World) := 
    {
      TCsupport w :> Type;
      Treadp w : TCsupport w -> w.(PLab) -> Inst Atom w.(QLab);
      Treadn w : TCsupport w -> w.(NLab) -> Inst Molecule w.(QLab);
      TreadE w : TCsupport w -> SoContexts w.(QLab);
      Textends w st: 
        forall v : Inst (TypingDec st) w.(QLab), TCsupport w -> TCsupport (wextends st w)
    }.

  (* The language of proof-terms is parameterised by:
- Patterns: type of elements that can be thought as patterns
To each pattern p is associated a tree skeleton PatDec p
   *)

  Class LAFs
        `(QST:QSTypes)
        (wextends : DecStruct -> World -> World)
        (TContext : TypingContexts wextends)
        (Patterns : Type)
        (PatDec   : Patterns -> DecStruct)
        (PatternsTyped : forall (p:Patterns) l, TypingDec (PatDec p) l -> Molecule l -> Prop)
    :=
      {
        wextends := wextends;
        TContext := TContext;
        Patterns := Patterns;
        PatDec   := PatDec;
        PatternsTyped := PatternsTyped
      }.

  Global Arguments PatternsTyped {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} p {l} _ _.

  (* We assume we have an instance of LAF *)

  Context `(LAF:LAFs).

  (***************)
  (* PROOF-TERMS *)
  (***************)

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

  Inductive Pos {w: World}:Type :=
  | pos: forall p: Patterns, @TermDec w (PatDec p) -> Pos
  with TermDec {w: World}: DecStruct -> Type :=
       | tleafP: w.(PLab) -> TermDec sleafP
       | tleafN: @Neg w -> TermDec sleafN
       | tdummy: TermDec sdummy
       | tnode {s1 s2}: @TermDec w s1 -> @TermDec w s2 -> TermDec (snode s1 s2)
       | tqnode {s}: Terms w.(QLab) -> @TermDec w s -> TermDec (sqnode s)
  with Neg {w: World}:Type :=
       | rei : (forall p:Patterns, @OptionCommand (wextends (PatDec p) w)) -> Neg
  with OptionCommand {w: World}: Type :=
       | some: @Command w -> OptionCommand
       | none
  with Command {w: World}: Type := 
       | cut   : @Neg w  -> @Pos w -> Command
       | select: w.(NLab) -> @Pos w -> Command.

  Global Arguments pos {w} p _.

  Scheme pos_ind :=
    Induction for Pos Sort Prop
    with termtree_ind :=
    Induction for TermDec Sort Prop
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

  Definition Reifiable w := forall p:Patterns, @OptionCommand (wextends (PatDec p) w).

  (* Notation "x + y" := (sum x y). *)
  (* Definition NegVar w := @Neg w + w.(NLab). *)

  Inductive cexists_as {w} : @OptionCommand w -> @Command w -> Prop :=
    cnotnone: forall o, cexists_as (some o) o
  .

  Notation "x =cis= y" := (cexists_as x y) (at level 30, right associativity).

  Lemma somecis {w u} {c: @Command w} : u =cis= c -> u = some c.
  Proof.
      by elim.
  Qed.

  (**********)
  (* TYPING *)
  (**********)

  (* This is the parameter that integrates the logical connectives.
It is a relation expressing:
"A formula can be decomposed into a TypingDec according to a pattern."
Example:
(A\/(B/\C)) can be decomposed into B,C according to the pattern inj2(_,_)
   *)

  (* Here is the typing system *)

  Inductive PosTyping {w} (Gamma: TContext w): @Pos w -> Inst Molecule w.(QLab) -> Prop :=
  | typingpos: forall p l v Delta A (tl:TList w.(QLab) l),
                 PatternsTyped p Delta A
                 -> DecTyping Gamma v Delta tl 
                 -> PosTyping Gamma (pos p v) [A,tl]
                             
  with DecTyping {w} (Gamma: TContext w)
       : forall l {st}, @TermDec w st -> TypingDec st l -> TList w.(QLab) l -> Prop :=
       | typingsub_leafl: forall l xp x (tl:TList w.(QLab) l),
                            is_eq (Treadp Gamma xp) [x,tl]
                            -> DecTyping Gamma (tleafP xp) (TleafP x) tl
       | typingsub_leafr: forall l nt A (tl:TList w.(QLab) l),
                            NegTyping Gamma nt [A,tl] ->
                            DecTyping Gamma (tleafN nt) (TleafN A) tl
       | typingsub_dummy: forall l (tl:TList w.(QLab) l),
                            DecTyping Gamma tdummy Tdummy tl
       | typingsub_node: forall l s1 s2 (v1:TermDec s1) (v2:TermDec s2)
                           Delta1 Delta2 (tl:TList w.(QLab) l),
                           DecTyping Gamma v1 Delta1 tl
                           -> DecTyping Gamma v2 Delta2 tl
                           -> DecTyping Gamma (tnode v1 v2) (Tnode Delta1 Delta2) tl
       | typingsub_qnode: forall l s (v:TermDec s) so Delta r (tl:TList w.(QLab) l),
                            SortingRel (TreadE Gamma) r so
                            -> DecTyping Gamma v Delta (TermCons so r tl)
                            -> DecTyping Gamma (tqnode r v) (Tqnode Delta) tl

  with NegTyping {w} (Gamma: TContext w) : @Neg w -> Inst Molecule w.(QLab) -> Prop :=
       | typingneg: forall f l A tl,
                      (forall p c, f p =cis= c -> exists Delta, PatternsTyped p Delta A)
                      ->
                      (forall p (Delta:TypingDec _ l), (PatternsTyped p Delta A)
                                              -> @OptionCommandTyping 
                                                  (wextends (PatDec p) w)
                                                  (Textends [Delta,tl] Gamma) 
                                                  (f p))
                      -> NegTyping Gamma (rei f) [A,tl]

  with OptionCommandTyping {w} (Gamma: TContext w): @OptionCommand w -> Prop :=
       | typingoption: forall c,
                         CommandTyping Gamma c
                         -> OptionCommandTyping Gamma (some c)

  with CommandTyping {w} (Gamma: TContext w): @Command w -> Prop :=
       | typingcut: forall nt pt A,
                      NegTyping Gamma nt A
                      -> PosTyping Gamma pt A
                      -> CommandTyping Gamma (cut nt pt)
       | typingselect: forall xn pt,
                         PosTyping Gamma pt (Treadn Gamma xn)
                         -> CommandTyping Gamma (select xn pt)
  .

  (* We create the induction principle on typing trees *)

  Scheme typingPos_ind := 
    Induction for PosTyping Sort Prop
    with typingSub_ind := 
    Induction for DecTyping Sort Prop
    with typingNeg_ind := 
      Induction for NegTyping Sort Prop
      with typingOptionCommand_ind := 
        Induction for OptionCommandTyping Sort Prop
        with typingCommand_ind := Induction for CommandTyping Sort Prop
  .

  Combined Scheme typing_ind from typingPos_ind, typingSub_ind, typingNeg_ind, typingOptionCommand_ind, typingCommand_ind.

  Record Contexts (A B C:Type)(D:QWorld -> Type) := 
    {
      Csupport w :> Type;
      readp w : Csupport w -> w.(PLab) -> A;
      readn w : Csupport w -> w.(NLab) -> B;
      readE w : Csupport w -> D w.(QLab);
      extends w st: 
        forall v : @Dec C A B st, @Csupport w -> @Csupport (wextends st w)
    }.

End LAF.

Notation "x =cis= y" := (cexists_as x y) (at level 30, right associativity).
