Require Import ssreflect.
Generalizable All Variables.
Typeclasses eauto := 1.

Record Test := { c: Type }.

Canonical build : Test :=
  {|
    c := Type
  |}
.

Print Canonical Projections.

Check (forall Q: c _, option Q).

(* On the other hand, the following fails!
Check (forall Q: c _, Q -> Q). 
But that works:
Check (forall Q: c _, (Q:Type) -> Q). 
*)

Record SClass {A:Type} (h:A) := {get : A := h}.
Arguments get {A h} _.

Class Test'
       `(super: SClass build)
  :=
    { 
      d : (get super).(c) ;
      e : d
    }.

Record TestClone := { from : Test}.

Canonical tosuper `(t:Test' super): TestClone := {| from := get super |}.

Definition f (t:TestClone) (x:c (from t)) := x.

Definition g1 `(t:Test' super)(x:Type) := option x.
Definition g2 `(t:Test' super)(x:c (get super)) := option x.

(* Ne marche plus *)

Definition h1 `(t:Test' super)(x:Type) := option (f _ x).
Definition h2 `(t:Test' super)(x:c (get super)) := option (f _ x).