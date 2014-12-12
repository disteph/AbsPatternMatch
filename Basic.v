Require Import Coq.Program.Equality.
Generalizable All Variables.

Notation "{{ p , v }}" := (existS _ p v).

Lemma elim2: forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
               {{p, x}} = {{p, y}} -> x = y.
Proof.
  exact inj_pair2.
Qed.
Arguments elim2 {U P p x y} _.

Record SClass {A:Type} (h:A) :=
  { IClass := A;
    get : A := h}.

Arguments IClass {A h} _.
Arguments get {A h} _.
