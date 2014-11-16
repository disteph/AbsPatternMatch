Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Open Scope type_scope.

Require Import ssreflect List Basic Equality.

Section QuantifyingStructure.
  (*************************)
  (* Quantifying Structure *)
  (*************************)

  Record QuantifyingStructures := 
    {
      Sorts : Type;
      QWorld: Type;
      Terms : QWorld -> Type;
      SoContexts: QWorld -> Type;
      SortingRel qLab : SoContexts qLab -> Terms qLab -> Sorts -> Prop
    }.

  (* We now assume we have a quantifying structure *)

  Variable QS: QuantifyingStructures.

  (**************************************)
  (* Useful definitions for types       *)
  (* (types are parameterised by terms) *)
  (**************************************)


  Inductive AList A : list QS.(Sorts) -> Type :=
  | TermNil   : AList A nil
  | TermCons s: A -> forall l, AList A l -> AList A (s::l).

  Definition TList (qLab:QS.(QWorld)) := AList (Terms qLab).

  Definition DPair A := {l: list QS.(Sorts) & A l}.

  Definition ex1 A (a:DPair A) := 
    match a with
      | existS l _ => l
    end.

  Definition ex2 A (a:DPair A): A (ex1 a) := 
    match a with
      | existS _ araw => araw
    end.

  Definition Inst A (qLab:QS.(QWorld)) := DPair (fun l => A l * TList qLab l).

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

Global Arguments Declift {E F A B C D} RelQ RelP RelN [st] _ _.

Lemma Decstruct {C A B: Type} st:
  match st with
    | sleafP => forall (v:Dec (C := C) (A := A) (B := B) sleafP), exists a, v = leafP a
    | sleafN => forall (v:Dec (C := C) (A := A) (B := B) sleafN), exists a, v = leafN a
    | sdummy => forall (v:Dec (C := C) (A := A) (B := B) sdummy), v = dummy
    | snode s1 s2 => forall (v:Dec (C := C) (A := A) (B := B) (snode s1 s2)),
                    exists (v1:Dec s1)(v2:Dec s2), v = node v1 v2
    | sqnode s0 => forall (v:Dec (C := C) (A := A) (B := B) (sqnode s0)),
                    exists (v0:Dec s0) t, v = qnode t v0
  end.
Proof.
  assert
    (forall (v:Dec (C := C) (A := A) (B := B) st),
      match st with
        | sleafP => exists a, JMeq v (leafP (C := C) (A := A) (B := B) a)
        | sleafN => exists a, JMeq v (leafN (C := C) (A := A) (B := B) a)
        | sdummy => JMeq v (dummy (C := C) (A := A) (B := B) )
        | snode s1 s2 => exists (v1:Dec s1)(v2:Dec s2), JMeq v (node (C := C) (A := A) (B := B) v1 v2)
        | sqnode s0 => exists (v0:Dec s0) t, JMeq v (qnode (C := C) (A := A) (B := B) t v0)
      end
    ).
  move => v.
  by case v;
  [
    move => a; exists a
  | move => b; exists b
  | 
  | move => s1 s2 v1 v2; exists v1; exists v2; apply JMeq_refl
  | move => s t v0; exists v0; exists t; apply JMeq_refl
  ].
  by move:H; case st
  =>  [ | | | s1 s2 | s ];
  move => H v; move:(H v); clear H;
         [ move => [a H]; exists a
         | move => [b H]; exists b 
         | move => H
         | move => [v1 [v2 H]]; exists v1; exists v2
         | move => [v0 [t H]]; exists v0; exists t
         ]
  ;
  apply JMeq_eq.
Qed.

Section LAF.

  (*********)
  (* TYPES *)
  (*********)

  (* The language of types is given by 
- Sorts:    sorts for terms
- Atom:     type of atoms
- Molecule: type of molecules *)

  Record QSTypes :=
    {
      QS :> QuantifyingStructures;
      Atom        : list QS.(Sorts) -> Type;
      Molecule    : list QS.(Sorts) -> Type;
      is_eq {qLab}: (Inst Atom qLab) -> (Inst Atom qLab) -> Prop
    }.

  Inductive TypingDec (QST: QSTypes): DecStruct -> list QST.(Sorts) -> Type  :=
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

  Record World (QS:QuantifyingStructures) :=
    {
      PLab:Type;
      NLab:Type;
      QLab:QS.(QWorld)
    }.

  Record Contexts {QS:QuantifyingStructures}
         (wextends: DecStruct -> World QS -> World QS)
         (A B C:Type)(D:QS.(QWorld) -> Type) := 
    {
      Csupport w :> Type;
      readp w : Csupport w -> w.(PLab) -> A;
      readn w : Csupport w -> w.(NLab) -> B;
      readE w : Csupport w -> D w.(QLab);
      extends w st: 
        forall v : @Dec C A B st, @Csupport w -> @Csupport (wextends st w)
    }.

  (* A typing context maps positive variables atoms and negative variables to molecules *)

  Record TypingContexts (QST:QSTypes)(wextends: DecStruct -> World QST -> World QST) := 
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

  Record LAFs :=
    {
      QST:> QSTypes;
      wextends : DecStruct -> World QST -> World QST;
      TContext : TypingContexts wextends;
      Patterns : Type;
      PatDec   : Patterns -> DecStruct;
      PatternsTyped (p:Patterns) l : @TypingDec QST (PatDec p) l -> Molecule l -> Prop
    }.

  Global Arguments TContext {_}.
  Global Arguments PatternsTyped {_} p {_} _ _.

  (* We assume we have an instance of LAF *)

  Variable LAF:LAFs.

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

  Inductive Pos (w: World LAF):Type :=
  | pos: forall p: LAF.(Patterns), TermDec w (PatDec p) -> Pos w
  with TermDec (w: World LAF): DecStruct -> Type :=
       | tleafP: w.(PLab) -> TermDec w sleafP
       | tleafN: Neg w -> TermDec w sleafN
       | tdummy: TermDec w sdummy
       | tnode {s1 s2}: TermDec w s1 -> TermDec w s2 -> TermDec w (snode s1 s2)
       | tqnode {s}: Terms w.(QLab) -> TermDec w s -> TermDec w (sqnode s)
  with Neg (w: World LAF):Type :=
       | rei : (forall p:LAF.(Patterns), OptionCommand (wextends (PatDec p) w)) -> Neg w
  with OptionCommand (w: World LAF): Type :=
       | some: Command w -> OptionCommand w
       | none
  with Command (w: World LAF): Type := 
       | cut   : Neg w  -> Pos w -> Command w
       | select: w.(NLab) -> Pos w -> Command w.

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

  Definition Reifiable w := forall p:Patterns LAF, OptionCommand (wextends (PatDec p) w).

  (* Notation "x + y" := (sum x y). *)
  (* Definition NegVar w := @Neg w + w.(NLab). *)

  Inductive cexists_as {w} : OptionCommand w -> Command w -> Prop :=
    cnotnone: forall o, cexists_as (some o) o
  .

  Notation "x =cis= y" := (cexists_as x y) (at level 30, right associativity).

  Lemma somecis {w u} {c: Command w} : u =cis= c -> u = some c.
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

  Inductive PosTyping {w} (Gamma: TContext w): Pos w -> Inst Molecule w.(QLab) -> Prop :=
  | typingpos: forall p l v Delta A (tl:TList w.(QLab) l),
                 PatternsTyped p Delta A
                 -> DecTyping Gamma v Delta tl 
                 -> PosTyping Gamma (pos p v) [A,tl]
                             
  with DecTyping {w} (Gamma: TContext w)
       : forall l {st}, TermDec w st -> TypingDec st l -> TList w.(QLab) l -> Prop :=
       | typingsub_leafl: forall l xp x (tl:TList w.(QLab) l),
                            is_eq (Treadp Gamma xp) [x,tl]
                            -> DecTyping Gamma (tleafP xp) (TleafP x) tl
       | typingsub_leafr: forall l nt A (tl:TList w.(QLab) l),
                            NegTyping Gamma nt [A,tl] ->
                            DecTyping Gamma (tleafN nt) (TleafN A) tl
       | typingsub_dummy: forall l (tl:TList w.(QLab) l),
                            DecTyping Gamma (tdummy w) Tdummy tl
       | typingsub_node: forall l s1 s2 (v1:TermDec w s1) (v2:TermDec w s2)
                           Delta1 Delta2 (tl:TList w.(QLab) l),
                           DecTyping Gamma v1 Delta1 tl
                           -> DecTyping Gamma v2 Delta2 tl
                           -> DecTyping Gamma (tnode v1 v2) (Tnode Delta1 Delta2) tl
       | typingsub_qnode: forall l s (v:TermDec w s) so Delta r (tl:TList w.(QLab) l),
                            SortingRel (TreadE Gamma) r so
                            -> DecTyping Gamma v Delta (TermCons so r tl)
                            -> DecTyping Gamma (tqnode r v) (Tqnode Delta) tl

  with NegTyping {w} (Gamma: TContext w) : Neg w -> Inst Molecule w.(QLab) -> Prop :=
       | typingneg: forall f l A tl,
                      (forall p c, f p =cis= c -> exists Delta, PatternsTyped p Delta A)
                      ->
                      (forall p (Delta:TypingDec _ l), (PatternsTyped p Delta A)
                                              -> OptionCommandTyping 
                                                  (w := wextends (PatDec p) w)
                                                  (Textends [Delta,tl] Gamma) 
                                                  (f p))
                      -> NegTyping Gamma (rei f) [A,tl]

  with OptionCommandTyping {w} (Gamma: TContext w): OptionCommand w -> Prop :=
       | typingoption: forall c,
                         CommandTyping Gamma c
                         -> OptionCommandTyping Gamma (some c)

  with CommandTyping {w} (Gamma: TContext w): Command w -> Prop :=
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


End LAF.

Notation "x =cis= y" := (cexists_as x y) (at level 30, right associativity).
