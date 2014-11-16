Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.
Typeclasses eauto := 1.

Require Import ssreflect Basic LAF LAFwE Semantics List Coq.Program.Equality.

Section SemanticswE.

  Context `(LAFwE: LAFswE).
  
  Definition MSwE2MS_base STermsV SLabV SPosV SNegV orthV SContextsV tildV SemTermsV IV
    :=
      {|
        STerms   := STermsV;
        Valuations := fun qLab: QWorld _ => (qLab:Type) -> STermsV;
        SLab     := SLabV;
        SPos     := SPosV;
        SNeg     := SNegV;
        orth     := orthV;
        SContexts := SContextsV;
        tild     := tildV;
        SemTerms := SemTermsV;
        I        := IV
      |}.
  
  Class ModelStructureswE
        {STermsV SLabV SPosV SNegV orthV SContextsV tildV SemTermsV IV}
    := 
    {
      asMS : SClass (@MSwE2MS_base STermsV SLabV SPosV SNegV 
                                   orthV SContextsV tildV SemTermsV IV);

      qLabSem qLab (xq:qLab)(sigma:Valuations (get asMS) qLab) 
      : SemTermsV _ sigma (asT xq) = sigma xq;

      reSem qLab qLab' (pi:qLab -> qLab')
            (r:Terms qLab)(tau:Valuations (get asMS) qLab') sigma:
        (forall xq, tau(pi xq) = sigma xq)
        -> SemTermsV _ tau (lift2Terms pi r) = SemTermsV _ (sigma:Valuations (get asMS) qLab) r;

      SrenProp: renProp (SContexts (get asMS));
      SstProp: stProp (SContexts (get asMS))

    }
  .

  Canonical MSwE2MS `(ModelStructureswE)
    := @MSwE2MS_base STermsV SLabV SPosV SNegV orthV SContextsV tildV SemTermsV IV.

  Definition RAwE2RA_base `(MSwE:ModelStructureswE)
      welfV SemSortsV SemSoCompatV SemAtomV SemAtom_eqV
    :=
    {| 
      modelStructure := MSwE2MS MSwE;
      welf := welfV;
      SemSorts := SemSortsV;
      SemSoCont := fun qLab Sigma (sigma: Valuations (MSwE2MS MSwE) qLab) 
                  => forall xq:qLab, SemSortsV (Sigma xq) (sigma xq);
      SemSoCompat := SemSoCompatV;
      SemAtom := SemAtomV;
      SemAtom_eq := SemAtom_eqV
    |}.

  Class RealisabilityAlgwE `(MSwE:ModelStructureswE)
         {welfV SemSortsV SemSoCompatV SemAtomV SemAtom_eqV}
    :=
    { 
      asMSwE := MSwE;
      asRA := RAwE2RA_base welfV (SemSortsV := SemSortsV) 
                          SemSoCompatV (SemAtomV := SemAtomV) SemAtom_eqV
    }.

  Coercion asMSwE: RealisabilityAlgwE >-> ModelStructureswE.
  Canonical RAwE2RA `(RAwE:RealisabilityAlgwE)
    := RAwE2RA_base welfV SemSoCompatV SemAtom_eqV.
  
  Lemma Rem53 `{M: RealisabilityAlgwE} w :
    forall (Gamma: TCV w.(QLab) w)(rho : SContexts _ w),
      SemCont (LAF:= LAFwE2LAF LAFwE) Gamma rho <-> 
      Contlift SemSorts (Pard SemAtom (readE rho)) (Pard (SemNeg (M:= RAwE2RA M)) (readE rho)) Gamma rho.
  Proof.
    done.
  Qed.

  Definition TypingCorrwE_Prop `(RA: RealisabilityAlgwE) :=
    forall qLab sigma, GenericCorr
                (Context1 := TCV qLab)
                (Context2 := SContexts (RAwE2RA RA))
                SemSorts
                (Pard SemAtom sigma)
                (Pard (SemNeg (M:= RAwE2RA RA)) sigma).

  Lemma SemTermListRen  `(MSwE:ModelStructureswE)
        {QLab QLab'} (ren:QLab -> QLab') tau sigma
        l tl:
    (forall xq, tau(ren xq) = sigma xq)
    -> SemTermList (M := MSwE2MS MSwE) (l := l) sigma tl
    = SemTermList (M := MSwE2MS MSwE) tau (renTList ren tl).
  Proof.
    intros.
    induction l;
    dependent inversion tl =>//=.
    rewrite (reSem _ (pi := ren)(tau := tau)(sigma := sigma)) =>//.
    by rewrite IHl.
  Qed.

  Definition correctNaming {E A B C D:Type} {qVar st} (Sigma: qVar -> E) v nametree
    := Declift (st:=st) (A:=A) (B:=B) (C:=C) (D:=D)
              (fun s q => s = Sigma q)
              (fun _ _ => True)
              (fun _ _ => True)
              v nametree.

  Lemma TDec2Dec `{RA: RealisabilityAlgwE}
        qLab
        (tau: Valuations (RAwE2RA RA) qLab)
        l
        (tl:TList qLab l)
        (st:DecStruct)
        (Delta:TypingDec st l)
        (qnew: @Dec qLab unit unit st)
        (v:SDec st)
  : correctNaming tau v qnew
    -> SemTDec Delta (SemTermList tau tl) v
    -> Declift SemSorts (Pard SemAtom tau) (Pard SemNeg tau) (InstTypingDec qnew tl Delta) v.
  Proof.
    by induction Delta;
    [ move:(Decstruct sleafP qnew)(Decstruct sleafP v)
      => [a' rqnew] [b' rv]; rewrite rqnew rv; clear rqnew rv qnew v
    | move:(Decstruct sleafN qnew)(Decstruct sleafN v)
      => [a' rqnew] [b' rv]; rewrite rqnew rv; clear rqnew rv qnew v
    | move:(Decstruct sdummy qnew)(Decstruct sdummy v)
      => rqnew rv; rewrite rqnew rv; clear rqnew rv qnew v
    | move:(Decstruct (snode _ _) qnew)(Decstruct (snode _ _) v)
      => [qnew1 [qnew2 rqnew]] [v1' [v2' rv]]; rewrite rqnew rv; clear rqnew rv qnew v;
        move => [H1 H2] [H3 H4]; split; [ apply IHDelta1 | apply IHDelta2 ]
    | move:(Decstruct (sqnode _) qnew)(Decstruct (sqnode _) v)
      => [qnew1 [xq rqnew]] [v' [t rv]]; rewrite rqnew rv; clear rqnew rv qnew v; simpl;
        move => [H1 H2] [H3 H4]; split; [ | apply IHDelta; [ | simpl; rewrite qLabSem -H1]]
    ].
  Qed.
  
  Lemma renContlift `{RA: RealisabilityAlgwE}
  : forall w  (rho : SContexts (RAwE2RA RA) w)
      (Gamma : TContext w) st (v:SDec st),
      Contlift SemSorts (Pard SemAtom (readE rho)) (Pard SemNeg (readE rho))
               Gamma rho
      ->
      Contlift SemSorts 
               (Pard SemAtom (readE (extends v rho)))
               (Pard SemNeg (readE (extends v rho)))
               (TCmap (renInst (Extren st)) (renInst (Extren st)) Gamma) 
               rho.
  Proof.    
    move => w rho Gamma st v.
    rewrite/Contlift/TCmap ;elim => H1 [H2 H3] /=.
    assert ( ContMap (fun i : Sorts (QSwE2QS LAFwE) => i) 
         (renInst (Extren st)) (renInst (Extren st)) Gamma
         ((let (TCstruct, TCmap, _) as TContextswE
              return
                (forall (qLab qLab' : Type) (w0 : World (get asQS)),
                 (Inst AtomV qLab -> Inst AtomV qLab') ->
                 (Inst MoleculeV qLab -> Inst MoleculeV qLab') ->
                 (TContextswE qLab) w0 -> (TContextswE qLab') w0) := TCV in
          TCmap) (QLab w) (QLab (wextendsE st w)) w 
                 (renInst (Extren st)) (renInst (Extren st)) Gamma)
           ).
    apply (TCmapProp (TContextswE:= TCV) (renInst (Extren st)) (renInst (Extren st)) Gamma ).
    case: H => [H4 [H5 H6]].
    split; [move => xq; clear H5 H6 |split; clear H4; [move => xp; clear H6 | move => xn; clear H5]].
    rewrite H4; apply H1.
    rewrite H5; clear H5 H1 H3.
    move:(H2 xp).
    refine (
        match readp Gamma xp as A return Pard SemAtom (readE rho) A (readp rho xp) -> Pard SemAtomV (readE (extends v rho))
     (renInst (Extren st) A) (readp rho xp)
        with
          | {{ l , A }} => _
        end
      ).
    elim A.
    rewrite /renInst/SemAtom/Pard/getA/getTerms/ex2 => a tl.
    simpl.
    rewrite <- (SemTermListRen _ (sigma := (readE rho))).
    done.
    apply SrenProp.
    rewrite H6; clear H6 H1 H2.
    move:(H3 xn).
    refine (
        match readn Gamma xn as A return Pard SemNeg (readE rho) A (readn rho xn) -> Pard SemNeg (readE (extends v rho))
     (renInst (Extren st) A) (readn rho xn)
        with
          | {{ l , A }} => _
        end
      ).
    elim A.
    rewrite /renInst/SemNeg/Pard/getA/getTerms/ex2 => a tl.
    simpl.
    rewrite <- (SemTermListRen _ (sigma := (readE rho))).
    done.
    apply SrenProp.
  Qed.
  
  Lemma Lem54 `(RA: RealisabilityAlgwE):
    TypingCorrwE_Prop RA -> TypingCorr_Prop (RAwE2RA RA).
  Proof.
    rewrite /TypingCorrwE_Prop/TypingCorr_Prop.
    move => H w st rho Gamma l Delta tl v H1 H2.
    move:(H (wextends st w).(QLab) (readE(extends v rho))) ; clear H => H.
    apply (Rem53 
             (Textends (t:=TContext) (w:=w) (st:=st) [Delta, tl] Gamma)
             (extends (c:=SContexts (RAwE2RA RA)) (w:=w) v rho)
          ).
    apply: H;
      [
      | move: (Rem53 Gamma rho) => [H3 _];
        move: (H3 H1);clear H1 H3 => H1; apply (renContlift v H1)].
    apply: TDec2Dec.
    apply: SstProp.
    rewrite /getA/getTerms/ex2.
    rewrite (SemTermListRen _ tl (ren:= Extren st)(sigma := readE rho)(tau := (readE (extends v rho)))) in H2.
    done.
    apply SrenProp.   
  Qed.


  Class FullModelwE `{RA: RealisabilityAlgwE} := 
    {
      asRAwE := RA;
      TypingCorrwE : TypingCorrwE_Prop RA;
      StabilitywE  : Stability_Prop (RAwE2RA RA)
    }.

  Coercion asRAwE: FullModelwE >-> RealisabilityAlgwE.

  Canonical FMwE2FM `(FullModelwE)
    := {|
        M0 := RAwE2RA RA;
        TypingCorr := Lem54 TypingCorrwE ;
        Stability := StabilitywE
      |}.

  Definition adequacywE `(FMwE: FullModelwE)
    := adequacy (FMwE2FM FMwE).

  (* Check adequacywE. *)
  
End SemanticswE.