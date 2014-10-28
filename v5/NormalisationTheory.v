Require Import ssreflect.

(* Reduction theory *)

Definition Rel (A B:Type) := A -> B -> Prop.
Definition Red (A:Type) := Rel A A.

Definition Sub {A B:Type} (R1 R2: Rel A B) : Prop := forall a b, R1 a b -> R2 a b.
Notation "R1 <# R2" := (Sub R1 R2) (at level 50).

Lemma SubRefl {A B:Type} (R: Rel A B) : Sub R R.
Proof.
  done.
Qed.

Lemma SubTrans {A B:Type} (R2 R1 R3: Rel A B) : Sub R1 R2 -> Sub R2 R3 -> Sub R1 R3.
Proof.
  rewrite/Sub.
  auto.
Qed.

Definition Equiv {A B:Type} (R1 R2: Rel A B) := Sub R1 R2 /\ Sub R2 R1.
Notation "R1 -- R2" := (Equiv R1 R2) (at level 50).

Inductive comp {A B C:Type} (red1: Rel A B)(red2: Rel B C) : Rel A C :=
  compose: forall b a c,  red1 a b -> red2 b c -> comp red1 red2 a c
.
Notation "R1 # R2" := (comp R1 R2) (at level 40).
Arguments compose {A B C red1 red2} _ _ _ _ _ .

Inductive inverse {A B:Type} (R: Rel A B) : Rel B A :=
  inverseof: forall a b, R a b -> inverse R b a
.

Lemma compTrans {A B C D:Type} (R1: Rel A B)(R2: Rel B C)(R3: Rel C D)
  : (R1 # R2) # R3 -- R1 # (R2#R3).
Proof.
  rewrite /Equiv; split.
  rewrite/Sub.
  move => a b H.
  inversion H.
  inversion H0.
  apply (compose b1) => //.
  apply (compose b0) => //.
  rewrite/Sub.
  move => a b H.
  inversion H.
  inversion H1.
  apply (compose b1) => //.
  apply (compose b0) => //.
Qed.

Lemma SubComp {A B C:Type} (R1 R2: Rel A B)(R3 R4: Rel B C) 
: Sub R1 R2 -> Sub R3 R4 -> Sub (comp R1 R3)(comp R2 R4).
Proof.
  rewrite/Sub.
  move => H1 H2 a b; elim => a0 b0 c0 H3 H4.
  apply (compose a0).
  auto.
  auto.
Qed.


Inductive trans {A:Type} (red: Red A) : Red A :=
| singl: forall a b,  red a b -> trans red a b
| transit: forall b a c,  red a b -> trans red b c -> trans red a c
.

Arguments transit {A} {red} _ _ _ _ _ .

Lemma transSub {A:Type} (red: Red A) : Sub red (trans red).
Proof.
  rewrite /Sub.
  move => a b H.
  apply singl => //.
Qed.

Lemma tailtransit {A red}: forall (b a c:A),  trans red a b -> trans red b c -> trans red a c.
Proof.
  move => a b c H1 H2.
  induction H1.
  apply (transit b) =>//.
  apply (transit b) =>//.
  apply IHtrans =>//.
Qed.

Lemma SubTrans1 {A:Type} (red1 red2: Red A) : Sub red1 red2 -> Sub (trans red1)(trans red2).
Proof.
  rewrite /Sub => H a b H0.
  induction H0.
  apply singl.
  auto.
  apply (transit b) => //.
  auto.
Qed.

Inductive Image {A B:Type} (R:Rel A B)(P: A -> Prop): B -> Prop
  := image: forall a b, P a -> R a b -> Image R P b.

Arguments image {A B R P} _ _ _ _.

(* Simulations *)

Definition StrongSimul {A B:Type} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  Sub (comp (inverse R) redA) (comp (trans redB) (inverse R)).

Lemma SimulMonotonic {A B:Type} (redA1 redA2: Red A) (redB1 redB2: Red B) (R: Rel A B):
  Sub redA2 redA1 -> Sub redB1 redB2 -> StrongSimul redA1 redB1 R -> StrongSimul redA2 redB2 R.
Proof.
  move => H1 H2.
  rewrite /StrongSimul.
  move => H3.
  apply (SubTrans (comp (inverse R) redA1)).
  apply SubComp =>//.
  apply: SubRefl.
  apply (SubTrans (comp (trans redB1) (inverse R))) => //.
  apply SubComp =>//.
  apply SubTrans1 => //.
Qed.

Lemma SimulBoth {A B:Type} (redA1 redA2: Red A) (redB: Red B) (R: Rel A B):
  StrongSimul redA1 redB R
  -> StrongSimul redA2 redB R
  -> StrongSimul (comp redA1 redA2) redB R.
Proof.
  rewrite /StrongSimul.
  move => H1 H2.
  rewrite/Sub => a b H3.
  inversion H3; clear H3.
  clear H4 H5 a0 c.
  inversion H0; clear H0.
  clear H5 H6 a0 c.
  rewrite /Sub in H1.
  have: ((inverse R # redA1) a b1).
  apply: (compose b0) =>//.
  move => H5; move: (H1 a b1 H5); clear H1 => H1.
  inversion H1; clear H1.
  clear H7 H8 H5 a0 c.
  have: ((inverse R # redA2) b2 b).
  apply: (compose b1) =>//.
  move => H5; move: (H2 _ _ H5); clear H2 => H2.
  inversion H2; clear H2.
  clear H9 H8 H5 a0 c.
  apply: (compose b3) =>//.
  apply: (tailtransit b2) => //.
Qed.

Lemma SimulTrans {A B:Type} (redA: Red A) (redB: Red B) (R: Rel A B)
: StrongSimul redA redB R -> StrongSimul (trans redA) redB R.
Proof.
  rewrite /StrongSimul.
  move => H.
  rewrite/Sub => b a H0.
  inversion H0.
  clear H3 H4 a0 c H0.
  move : b H1.
  induction H2.
  move => b0 H1.
  rewrite /Sub in H.
  have : ((inverse R # redA) b0 b).
  apply: (compose a) => //.
  move => H5.
  move: (H _ _ H5) =>//.
  move => b0 H1.
  have:((inverse R # redA) b0 b).
  apply:(compose a) => //.
  clear H1 => H1.
  move: (H _ _ H1); clear H1 H => H.
  inversion H.
  clear H4 H5 a0 c0.
  move: (IHtrans _ H3); clear IHtrans H3.
  move => H3.
  inversion H3.
  clear H6 H7 a0 c0.
  apply: (compose b2) => //.
  apply: (tailtransit b1) => //.
Qed.

Inductive refltrans {A:Type} (red: Red A) : Red A :=
| reflex: forall a,  refltrans red a a
| atleast1: forall a b,  trans red a b -> refltrans red a b
.

Lemma trans2refltrans {A} {red: Red A}: trans red -- red # (refltrans red).
Proof.
  rewrite /Equiv/Sub.
  split => a b H.
  inversion H.
  apply:(compose b) => //.
  apply reflex.
  apply:(compose b0) => //.
  apply atleast1 =>//.
  inversion H.
  inversion H1.
  apply:(singl).
  rewrite H5 in H0 => //.
  apply:(transit b0) =>//.
Qed.

(* Strong Normalisation theory *)

Definition patriarchal {A:Type} (red:Red A) (P:A -> Prop): Prop
  := forall x, (forall y, red x y -> P y) -> P x.

Definition SN {A:Type} (red:Red A) (a:A): Prop
  := forall P, patriarchal red P -> P a.

Lemma toSN {A:Type}{red:Red A} {x}: (forall y, red x y -> SN red y) -> SN red x.
Proof.
  rewrite/SN => H P H1.
  move:(H1); rewrite/patriarchal.
  apply => y H2.
  apply H => //.
Qed.

Lemma SNpatriarchal {A} {red: Red A}: patriarchal red (SN red). 
Proof.
  rewrite /patriarchal => M H.
  rewrite/SN => P H1; apply: (H1); intros.
  move: (H y H0).
  apply => //.
Qed.

Lemma SNstable {A} {red: Red A}: forall M, SN red M -> forall N, red M N -> SN red N.
Proof.
  have : (patriarchal red (fun a => forall b, red a b -> SN red b)).
  move => P /= H.
  move : (@SNpatriarchal A red) => H1.
  rewrite /patriarchal in H1 => R HR.
  apply: H1.
  apply: H => //.
               intros.            
    by apply (H _ x).
Qed.

Theorem SNind {A} {red: Red A} {P: A -> Prop}
: (forall a, (forall b, red a b -> P b) -> SN red a -> P a)
  -> (forall a, SN red a -> P a).
Proof.
  move => H3.
  have: (patriarchal red (fun a => SN red a -> P a)).
  rewrite /patriarchal => N H H0.
  apply: H3 =>//.
            move => R H2.
  apply: H => //.
               apply (SNstable N) => //.
                                      move => H0 M H1.
  apply: (H1 (fun a : A => SN red a -> P a)) => //.
Qed.

Lemma Patriarchalmonotonic {A} {red1 red2: Red A}: 
  red1 <# red2 -> forall P, patriarchal red1 P -> patriarchal red2 P.
Proof.
  rewrite /Sub/patriarchal => H0 P H1 a H2.
  apply: H1.
  move => y H1.
  apply: H2.
  apply H0 =>//.
Qed.

Lemma SNmonotonic {A} {red1 red2: Red A}: red1 <# red2 -> forall a, SN red2 a -> SN red1 a.
Proof.
  rewrite/SN.
  move => H0 a H1 P H2.
  apply: H1.
  apply: (Patriarchalmonotonic H0 P H2).
Qed.

Lemma SNSNtrans {A} {red: Red A}: forall a, SN red a <-> SN (trans red) a.
Proof.
  split;[| apply: SNmonotonic => //; apply transSub].
  have: (forall M, SN red M -> forall N, refltrans red M N -> SN (trans red) N).
  apply (@SNind _ _ (fun M => forall N, refltrans red M N -> SN (trans red) N)).
  move => M IH MSN.
  have:(forall N, trans red M N -> SN (trans red) N).
  move => N H.
  move: (proj1 trans2refltrans _ _ H); clear H => H.
  inversion H.
  apply:(IH b) => //.
  move => H.
  move: (@SNpatriarchal _ (trans red)).
  rewrite/patriarchal.
  move => H1.
  move: (H1 M H); clear H H1 => H N H1.
  inversion H1.
  by rewrite <- H2.
  apply:(SNstable M) => //.
  intros.
  apply:(x a) =>//.
  apply: reflex.
Qed.

Theorem SNsind {A} {red: Red A} {P: A -> Prop}
: (forall a, (forall b, trans red a b -> P b) -> SN red a -> P a)
  -> (forall a, SN red a -> P a).
Proof.
  move => H a H0.
  move: (proj1(SNSNtrans a)H0).
  clear H0; move: a.
  apply SNind.
  move => a H0 H1.
  apply H => //.
  apply SNSNtrans =>//.
Qed.

Theorem SNbySimul {A B} {redA: Red A} {redB: Red B} {R: Rel A B}:
StrongSimul redA redB R -> forall a, Image (inverse R) (SN redB) a -> SN redA a.
Proof.
  move => H M H0.
  inversion H0; clear H0 H3 b.
  move : a H1 M H2.
  apply (@SNsind _ _ (fun a => forall M : A, inverse R a M -> SN redA M)).
  move => N H0 SNN M H1.
  apply SNpatriarchal => M' H2.
  rewrite /StrongSimul/Sub in H.
  have:((inverse R # redA) N M').
  apply: (compose M)=>//.
  move => H3.
  move:(H _ _ H3); clear H H3 => H.
  inversion H; clear H5 H6 a c.
  apply:(H0 b) =>//.
Qed.