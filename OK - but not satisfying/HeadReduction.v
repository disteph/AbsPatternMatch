Require Import ssreflect SyntaxTyping Semantics NormalisationTheory Basic.

Definition SPrim {w} := option w.(PVar).

Definition SNContext_fun A w
  := @ContType (@SPrim w) ({w':World &  (A w w' £ @Neg w')} + w.(NVar)).
Inductive SNContext_aux wnew w := { sncontext : SNContext_fun SNContext_aux wnew w}.
Definition SNContext := SNContext_fun SNContext_aux.

Definition SNeg {wnew} := {w:World & (@SNContext_aux wnew w £ @Neg w)} + wnew.(NVar).
Notation "<< x , y >>" := (inl(existS (fun w' => SNContext_aux _ w' £ _ w')
                                     _
                                     ({| sncontext := x |},y))).

Definition STree {w st} := @Tree (@SPrim w) (@SNeg w) st.
Definition SPos {w}     := {p:Patterns & @STree w (PatTree p)}.
Definition Pair {w}     := (@SNeg w) £ (@SPos w).

Lemma TermTreeSemTree : 
  forall w wnew (rho:SNContext wnew w) st, @TermTree w st ->  @STree wnew st.
Proof.
  move => w wnew rho.
  elim.
  move => v; inversion v ;  exact (leafP (rho.(readp) X)).
  move => v; inversion v. refine (leafN (<< rho , X >>)).
  move => s1 H1 s2 H2 v; inversion v; exact (node (H1 X)(H2 X0)).
Defined.
Arguments TermTreeSemTree {w wnew} rho {st} _ .

Definition PosSemP {w wnew} (rho:SNContext wnew w) (tp: @Pos w):@SPos wnew :=
  match tp with
    | pos p v => {{ p,TermTreeSemTree rho v }}
  end.

Definition CommandSemC {w wnew} (rho:SNContext wnew w) (c: @Command w):@Pair wnew :=
  match c with
    | cut tn tp => (<< rho, tn >>, PosSemP rho tp)
    | select xn tp => (rho.(readn) xn, PosSemP rho tp)
  end.

Inductive HeadReduction {w} : @Pair w ->  @Pair w -> Prop :=
| betared:
    forall w1 (rho:SNContext w w1) (f: @Reifiable w1) (p: Patterns) (v: STree) c,
      f p =cis= c
      -> HeadReduction
          (<< rho , rei f >>, {{ p, v }})
          (CommandSemC (Context.(extends) v rho) c).

Section Normalisation.

  Variable wnew: World.
  Variable xn0: wnew.(NVar).

  Definition SubsModel
    := {| 
        primitives := @SPrim wnew; 
        negatives := @SNeg wnew;
        positives := @SPos wnew;
        orth := SN HeadReduction
      |}.

  Definition SubsFullModelRaw
    := {| 
        model := SubsModel;
        tild := fun p v => {{ p , v }};
        I := fun w f rho => << rho , rei f >>
      |}.

  Lemma goodsub {w} : forall rho st (v:@TermTree w st), 
                        SemSub SubsFullModelRaw rho v = TermTreeSemTree rho v.
  Proof.
    move => rho.
    elim.
      by move => v ; dependent inversion v.
        by move => v ; dependent inversion v; elim n => f.      
        move => s1 H1 s2 H2; dependent inversion v => /=; by rewrite H1 H2.
  Qed.


  Definition SNgood (sigma :tvaluation SubsFullModelRaw) := forall fvar pri, sigma fvar pri.

  Lemma Negnonempty {sigma}{H0:SNgood sigma}: forall A, exists n, SemNeg SubsFullModelRaw sigma A n.
  Proof.
    move => A.
    exists (inr xn0).
    rewrite/SemNeg/ortho => tp _.
    elim:tp =>//.
            move => p v.
    simpl.
    apply toSN => y H.
    inversion H.
  Qed.

  Lemma Treenonempty {sigma}{H0:SNgood sigma}: forall st Delta, exists v, @SemCont SubsFullModelRaw sigma st Delta v.
  Proof.
    elim.
    move => Delta; dependent inversion Delta ; by exists (leafP None).
                                           move => Delta; dependent inversion Delta; elim:(Negnonempty (H0:=H0) f) => n H ; by exists (leafN n).
                                                                                                                       move => s1 H1 s2 H2 Delta; dependent inversion Delta.
                                                                                                                       elim: (H1 t) => v1 H5.
                                                                                                                       elim: (H2 t0) => v2 H6.
                                                                                                                       exists (node v1 v2).
                                                                                                                       split =>//.
  Qed.

  Hypothesis alwaysPat: forall A, exists p Delta, PatternsTyped p Delta A.

  Lemma Posnonempty sigma (H0:SNgood sigma): forall A, exists pt, SemPos SubsFullModelRaw sigma A pt.
  Proof.
    move => A.
    elim:(alwaysPat A)=> p; elim => Delta H1.
    elim:(Treenonempty (H0 := H0) (PatTree p) Delta) => v H2.
    refine (ex_intro _ _ _).
    apply SemPosCont.
    apply (pv _ sigma A _ p Delta) =>//.
          exact H2.
  Qed.

  Definition SNVS :=
    {|
      MW := SubsFullModelRaw ;
      Pvalue := fun _ => True;
      Nvalue := fun n => exists tp, SubsFullModelRaw.(orth) (n,tp);
      orthVal := fun tn tp H => ex_intro _ tp H;
      goodtval := SNgood;
      goodIgood := fun _ _ _ _ _ => Logic.I;
      nonempty := Posnonempty
    |}.


  Lemma stabsubs {w} :
    forall (f: Reifiable) (rho: SContext SNVS w) (p: Patterns) (v: SemTree (PatTree p))  c,
      valuesTree SNVS v
      -> f p =cis= c
      -> SNVS.(orth) (SemC SNVS (Context.(extends) v rho) c)
      -> SNVS.(orth) (SNVS.(I) f rho, SNVS.(tild) p v).
  Proof.
    move => f rho p v c H0 H1 H2.
    apply toSN => x' H3.
    inversion H3.
    move: (elim2 H5); clear H5 => H5.
    move: (elim2 H6); clear H6 => H6.
    move: (elim2 H8); clear H8 => H8.
    clear H4 H3 x'.
    rewrite H5;clear H5 .
    rewrite H8;clear H8 v1.
    rewrite H6 in H9;clear H6 f1.
    clear H7 p0.
    clear H w1.
    move:(somecis H9) ; clear H9.
    move:(somecis H1); clear H1.
    move => H; rewrite H.
    move => H'; injection H'; clear H'.
    move => H'; rewrite <- H'.
    clear c0 H'.
    elim: c H2 H.
    + move => tn tp H _.
      elim: tn H => f' H.
      elim: tp H => p' v' H /=.
                      rewrite <- goodsub =>//.
                   + move => xn tp H _.
      elim: tp H => p' v' H /=.
                      rewrite <- goodsub.
      done.
  Qed.

  Definition SNFVS :=
    {|
      VS := SNVS ;
      stabVS := @stabsubs
    |}.

  Definition sigmatriv:tvaluation SubsFullModelRaw := fun _ _ => True.
  Lemma sigmatrivgood: SNgood sigmatriv.
  Proof.
    done.
  Qed.

  Definition rhotriv : SContext SNVS wnew
    := {| readp := fun xp => Some xp;
         readn := fun xn => inr xn |}.

  Lemma rhotrivgood {Gamma}: compat (toFM SNFVS) sigmatriv Gamma rhotriv.
  Proof.
    rewrite/compat/sigmatriv.
    simpl.
    split; [ done |].
    move => xn.
    rewrite/SemNeg/ortho/orth.
    elim => p v _.
    simpl.
    apply toSN => y H.
    inversion H.
  Qed.

  Theorem HeadNormalisation: 
    forall Gamma c, TypingCommand Gamma c -> SN HeadReduction (CommandSemC rhotriv c).
  Proof.
    move => Gamma c H.
    elim: (NEadequacy SNFVS sigmatriv sigmatrivgood wnew Gamma) => _ ;
                                                           elim => _;
                                                                  elim => _;
                                                                         elim => _ H'.
    move:(H' c H rhotriv rhotrivgood); clear H' H.
    simpl.
    elim:c.
    simpl.
    rewrite /SemC.
    elim => f'.
    elim => p' v' /=.
              rewrite <- goodsub.
    apply.
    move => xn p _.
    apply toSN => y H.
    inversion H.
  Qed.

End Normalisation.

Print Assumptions HeadNormalisation.