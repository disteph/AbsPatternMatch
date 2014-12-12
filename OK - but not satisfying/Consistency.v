Require Import ssreflect SyntaxTyping Semantics. 

Variable MyPVar:Type.

Definition EmptyWorld := {| PVar := MyPVar; NVar := False |}.

Definition TrivialModel := {| primitives := unit; 
                             positives := unit; 
                             negatives := unit; 
                             orth := (fun _ => False)|}.

Definition TrivialFullModelRaw := {| 
                                   model := TrivialModel;
                                   tild := (fun _ _ => tt);
                                   I := (fun _ _ _ => tt)
                                 |}.

Lemma emptystab : forall w,
                    let M0 := TrivialFullModelRaw in
                    forall (f: Reifiable) (rho: SContext M0 w)
                      (p: Patterns) (v: SemTree (PatTree p))  c,
                      True
                      -> (f p) =cis= c
                      -> M0.(orth) (SemC M0 (Context.(extends) v rho) c)
                      -> M0.(orth) (M0.(I) f rho, M0.(tild) p v).
Proof.
  done.
Qed.

Definition TrivialFullModel := {| M0 := TrivialFullModelRaw;
                                 treevalue := fun _ _ => True;
                                 stab := emptystab |}.

Lemma trivvalue sigma st (v:@SemTree TrivialFullModel st) Delta
: SemCont TrivialFullModel sigma Delta v -> treevalue TrivialFullModel v.
Proof.
  done.
Qed.

Definition trivsigma : tvaluation TrivialFullModel := fun _ _ => True.

Lemma EmptyEnvCompat: forall (Gamma:TContext EmptyWorld) 
                        (rho: SContext TrivialFullModel EmptyWorld), 
                        compat TrivialFullModel trivsigma Gamma rho.
Proof.
  move => Gamma rho.
  unfold compat.
  by split ; [|elim].
Qed.

Definition emptyEnv : SContext TrivialFullModel EmptyWorld :=
  {| readp := fun xp => tt;
     readn := fun xn => tt |}.

Theorem consistency: forall (Gamma:TContext EmptyWorld), forall c, TypingCommand Gamma c -> False.
Proof.
  move => Gamma c H.
  elim (adequacy TrivialFullModel trivsigma (trivvalue trivsigma) EmptyWorld Gamma) => _.
  elim => _ ; elim => _ ; elim => _ H1.
  apply: (H1 c H emptyEnv (EmptyEnvCompat _ _)).
Qed.

