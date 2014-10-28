Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Require Import ssreflect Basic LAF List Coq.Program.Equality Semantics.

Section SemanticsNE.

  Variable (LAF: LAFs).

  Record ValuesSystem(MW : RealisabilityAlg LAF) :=
    {
      isVal    : MW.(SNeg) -> Prop;
      orthVal  : forall tn tp, orth (tn,tp) -> isVal tn ;
      nonempty : forall st l (Delta:TypingDec st l) tl, exists v, SemTDec LAF MW Delta tl v;
      isValtriv {w}:
        forall rho (f:Reifiable w),
          (forall p c, f p =cis= c -> isVal (SemN rho (rei f)))
          -> isVal (SemN rho (rei f))
    }.

  Theorem TypedIsVal (M : FullModel LAF) (VS: ValuesSystem M):
    forall (w:World LAF) (Gamma:TContext w) (rho:M.(SContexts) w) nt A,
      NegTyping Gamma nt A ->  SemCont LAF M Gamma rho -> VS.(isVal) (SemN rho nt)
  .
  Proof.
    move => w Gamma rho nt A H0 H1.
    case: (adequacy M Gamma) => _ [_ [H _]].
    move:(H nt A H0 rho H1).
    move: H => _ .
    rewrite /Pard/SemNeg/getA/getTerms.
    case: H0 => /=; intros.
    apply: isValtriv => p c H2.
    move:(e p c H2).
    clear H1 A H2 e o.
    case => Delta H1.
    rewrite /ortho in H.
    case:(VS.(nonempty) Delta (SemTermList (readE rho) tl)) => v H2.
    move: (H (tild p v)) => H3.
    clear H.
    have: orth (I rho f, tild p v).
    apply:H3.
    apply SemPosDec.
    apply: (pv _ _ {{l,A0}} _ _ _ Delta) => //.
                                     clear H3.
    apply: orthVal.
  Qed.

  Print Assumptions TypedIsVal.

End SemanticsNE.

(* Fixpoint isDecVal {st} (v:SDec st) := *)
(*   match v with *)
(*     | leafP xp => True *)
(*     | leafN tm => VS.(isVal) tm *)
(*     | dummy    => True *)
(*     | node s1 s2 v1 v2 => isDecVal v1 /\ isDecVal v2 *)
(*     | qnode s r v' => isDecVal v' *)
(*   end *)
(* . *)

(* Lemma SemDecValues: forall st l (Delta:TypingDec st l) v tl, SemTDec (l := l) Delta tl v -> isDecVal v. *)
(* Proof. *)
(*   induction Delta; dependent induction v => tl //=. *)
(*     by move => [H1 _]. *)
(*     by move => [H1 H2]; split ; [apply (IHDelta1 _ tl) | apply (IHDelta2 _ tl) ]. *)
(*     by move => [H1 H2]; apply (IHDelta _ (TermCons c Logic.I tl)). *)
(* Qed. *)

