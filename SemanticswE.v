Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Unset Printing Implicit Defensive.
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
      : SemTerms sigma (asT xq) = sigma xq;
      reSem qLab qLab' (pi:qLab -> qLab')
            (r:Terms qLab)(sigma:Valuations (get asMS) qLab'):
        SemTerms sigma (lift2Terms pi r) = SemTerms ((comp sigma pi):Valuations (get asMS) qLab) r
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
  
  Definition TypingCorrwE_Prop `{M: RealisabilityAlgwE} :=
    forall qLab sigma, GenericCorr
                (Context1 := TCV qLab)
                (Context2 := SContexts _)
                SemSorts
                (Pard SemAtom sigma)
                (Pard (SemNeg (M:= RAwE2RA M)) sigma).

  Record FullModelwE `{M: RealisabilityAlgwE} := 
    {
      asRAwE := M;
      TypingCorrwE : TypingCorrwE_Prop;
      StabilitywE w :
        forall (f: Reifiable w) (rho: SContexts (RAwE2RA M) w) (p: Patterns (LAFwE2LAF LAFwE))
          l Delta (tl:STList (RAwE2RA M) l) (v: SDec (PatDec p)) c,
          f p =cis= c
          -> SemTDec Delta tl v
          -> orth (SemC (extends v rho) c)
          -> orth (I rho f, tild p v)
    }.

  Coercion asRAwE: FullModelwE >-> RealisabilityAlgwE.

End SemanticswE.


(* Lemma SemTermListRen {QVar QVar'}: *)
(*       forall (ren:QVar -> QVar') (sigma:@qvaluation M QVar) tau, *)
(*         (forall xq, tau (ren xq) = sigma xq) *)
(*         -> forall l tl, SemTermList (l := l) sigma tl = SemTermList tau (UTTermListRen ren tl). *)
(* Proof. *)
(*   intros. *)
(*   induction l. *)
(*   dependent inversion tl =>//. *)
(*   dependent inversion tl =>//=. *)
(*   rewrite (M.(SemTermsRen) (QVar := QVar) (QVar' := QVar') ren sigma tau) =>//. *)
(*   by rewrite IHl. *)
(* Qed. *)


(*   Lemma SemPos2Treelift  qVar qVar' (sigma:qvaluation qVar) (tau:qvaluation qVar') (ren:qVar -> qVar') st qnew l Delta (tl:UTTermList M.(terms) l) tl' v  *)
(*   :  (forall xq, tau (ren xq) = sigma xq) *)
(*      -> correctNaming tau v qnew *)
(*      -> tl = SemTermList M tau tl' *)
(*      -> SemTDec (M := M)(st := st) Delta tl v *)
(*      -> Treelift M.(sortsI) (Pard atomI tau) (Pard SemNeg tau) (namedTypeTree tl' Delta qnew) v. *)

(*   Proof. *)
(*     move : l Delta tl tl'. *)
(*     induction st => l Delta tl tl' H0 H1  H2; dependent induction v =>//=; dependent induction Delta =>//=; dependent induction qnew =>//=. *)
(*     rewrite /getA/getTerms/ex2.  *)
(*     by rewrite H2. *)
(*     rewrite /getA/getTerms/ex2.  *)
(*     by rewrite H2. *)
(*     simpl in H1.  *)
(*     elim: H1 => H3 H4. *)
(*     move => [I1 I2]; split ; [apply (IHst1 _ _ _ _ tl) | apply (IHst2 _ _ _ _ tl) ] =>//. *)
(*     simpl in H1.  *)
(*     elim: H1 => H3 H4. *)
(*     elim => H5 H6; split => //. *)
(*     clear IHv IHDelta IHqnew. *)
(*     apply (IHst _ _ _ _ (TermCons c Logic.I tl)) =>//. *)
(*     simpl. *)
(*     by rewrite SemTermsVar H3 H2. *)
(* Qed. *)

(*   Lemma compatrename w w' Gamma rho sigma tau (ren:w.(QVar) -> w'.(QVar)) *)
(*   (pi: forall xq, tau (ren xq) = sigma xq) *)
(*   : compat sigma Gamma rho -> compat tau (Contmap (w:=w) (fun i => i) (ParRen ren) (ParRen ren) Gamma) rho. *)
(*   Proof. *)
(*     rewrite/compat/Contlift/Contmap;elim => H1 [H2 H3] /=. *)
(*                                               split => //;split. *)
(*     move => xp. *)
(*     move: (H2 xp); clear H2 H3. *)
(*     elim : (readp Gamma xp) => l [a tl].  *)
(*     rewrite /Pard/ParRen/ex1/getA/getTerms/ex2; simpl. *)
(*     rewrite (SemTermListRen (QVar := w.(QVar)) (QVar' := w'.(QVar)) M ren sigma tau) =>//. *)
(*     move => xn. *)
(*     move: (H3 xn); clear H2 H3. *)
(*     elim : (readn Gamma xn) => l [a tl].  *)
(*     rewrite /Pard/ParRen/ex1/getA/getTerms/ex2; simpl. *)
(*     rewrite (SemTermListRen (QVar := w.(QVar)) (QVar' := w'.(QVar)) M ren sigma tau) =>//. *)
(* Qed. *)





(* apply (SemPos2Treelift _ _ rho.(readq) _ (qinject Context (PatTree p) w) (PatTree p) (qnew Context (PatTree p) w) l Delta (SemTermList M rho.(readq) tl) (UTTermListRen (qinject Context (PatTree p) w) tl))=> // . *)
(* move => xq. *)
(* apply (Context.(extends_qinject) (w:=w) (st:=PatTree p)). *)
(* apply (Context.(extends_qnew) (w:=w) (st:=PatTree p)). *)
(* apply SemTermListRen. *)
(* move => xq. *)
(* apply (Context.(extends_qinject) (w:=w) (st:=PatTree p)). *)
(* apply (compatrename _ _ _ _ rho.(readq)) => //. *)
(* move => xq. *)
(* apply (Context.(extends_qinject) (w:=w) (st:=PatTree p)). *)
