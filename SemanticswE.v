Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Unset Printing Implicit Defensive.

Require Import ssreflect Basic LAF List Coq.Program.Equality.

Variable LAF: LAFs.

Section TermSemantics.

  (* A model structure has five basic support sets: 
- term denotations,
- valuations (parameterised by a QWorld),
- label denotations, 
- positive and negative denotations;
Then we have
- an orthogonality relation between negative and positive denotations;
- a notion of semantic context
- an interpretation for patterns
- an interpretation for terms in a valuation in the correct QWorld
- an interpretation for the reifeied functions 
   *)
  
  Record ModelStructures := 
    {
      STerms   : Type;
      Valuations : LAF.(QWorld) -> Type;
      SLab     : Type;
      SPos     : Type;
      SNeg     : Type;
      orth     : SNeg*SPos -> Prop;
      SContexts: Contexts wextends SLab SNeg STerms Valuations;
      tild p   : @Dec STerms SLab SNeg (@PatDec LAF p) -> SPos;
      SemTerms {qLab} : Valuations qLab -> Terms qLab -> STerms;
      I {w} : SContexts w -> @Reifiable LAF w -> SNeg
    }
  .

  Global Arguments tild {_} p _.

  (* A useful abbreviation for semantical decompositions, which will
  interpret term decompositions *)

  Definition SDec {M} := @Dec M.(STerms) M.(SLab) M.(SNeg).

  (* We now suppose we have a model structure *)

  Variable M: ModelStructures.

  Definition STList := @AList LAF M.(STerms).

  Fixpoint SemTermList qVar sigma l (tl:TList qVar l) :STList l
    := match tl with
        | TermNil => TermNil _ _
        | TermCons so r l' tl' => TermCons so (SemTerms sigma r) (SemTermList sigma tl')
      end.

  (* The semantics of a negative term is a negative element of the model *)
  Definition SemN w (rho: M.(SContexts) w) (tm : Neg) := 
    match tm with
      | rei f => I rho f
    end
  .

  (* The semantics of a TermDec is a SemTree *)
  Fixpoint SemDec w (rho:M.(SContexts) w) {st} (v : TermDec st) {struct v} :=
    match v in @TermDec _ _ s return SDec s with
      | tleafP xp => leafP (readp rho xp)
      | tleafN tm => leafN (SemN rho tm)
      | tdummy    => dummy
      | tnode s1 s2 v1 v2 => node (SemDec rho (st:=s1) v1) (SemDec rho (st:=s2) v2)
      | tqnode s r v => qnode (SemTerms (readE rho) r) (SemDec rho (st:=s) v)
    end
  .

  (* The semantics of a positive term is a positive element of the model *)
  Definition SemP w (rho:M.(SContexts) w) (pt : Pos) := 
    match pt with
        pos p v => tild p (SemDec rho v)
    end
  .

  (* The semantics of a command is a pair (negative element,positive
element) of the model, that may or may not be orthogonal *) 

  Definition SemC w (rho:M.(SContexts) w) (c : Command) :=
    match c with
      | cut tm tp => (SemN rho tm,SemP rho tp) 
      | select xm tp => (rho.(readn) xm,SemP rho tp)
    end 
  .

  Definition SemOptionC w (rho:M.(SContexts) w)(oc : OptionCommand) :=
    match oc with
      | some c => Some(SemC (rho:M.(SContexts) w) c)
      | none => None
    end
  .

End TermSemantics.



Section TypeSemantics.

  (************************************************************************)
  (* We now want to define the semantical interpretation of types/formulae.

This is traditionally done "by induction on types/formulae".
In our setting, we do not have an inductive structure for types/formulae;
however, we know how to decompose molecules into atoms and
molecules.

Morally speaking, this corresponds to accessing sub-formulae, and
since the sub-formula relation is the well-founded relation that
allows to define the semantics of formulae, we will now assume the
well-foundedness of the relation between molecules induced by the
decomposition relation.

In other words, when a molecule is decomposed into a TypeTree
according to a pattern, then the molecules belonging to the TypeTree
have to be SMALLER than the decomposed molecule.

We formalise this. *)

  (* A molecule belongs to a TypeTree, as if it were a set *)

  Inductive  belong l
  : forall l' st, TypingDec (QST := LAF) st l' -> @Molecule LAF l -> Prop
    :=
    | rel_leaf  : forall B, belong (TleafN B) B
    | rel_node1 : forall B l' s1 s2 (t1:TypingDec s1 l') (t2:TypingDec s2 l'),
                    belong t1 B -> belong (Tnode t1 t2) B
    | rel_node2 : forall B l' s1 s2 (t1:TypingDec s1 l') (t2:TypingDec s2 l'),  
                    belong t2 B -> belong (Tnode t1 t2) B
    | rel_nodeq : forall so B l' s (t:TypingDec s (so::l')), 
                    belong t B
                    -> belong (Tqnode t) B
  .

  Inductive relation : DPair (@Molecule LAF) -> DPair (@Molecule LAF) -> Prop :=
    relation_base:
      forall p l l' Delta A B, PatternsTyped p Delta A
                      -> belong Delta B
                      -> relation (existS _ l B) (existS _ l' A).

  Global Arguments relation_base p {l l'} Delta A B _ _.

  (****************************************************************)
  (* We now define the semantics of types according to a ModelRaw *)

  Definition Pard {A B M} 
             (f: forall a:DPair A, STList M (ex1 a) -> B)
             {qLab} sigma a
    := f {{ ex1 a, getA (qLab := qLab) a }} (SemTermList sigma (getTerms a)).
  
  Record RealisabilityAlg :=
    { modelStructure :> ModelStructures;
      welf: well_founded relation;
      SemSorts : Sorts LAF -> modelStructure.(STerms) -> Prop;
      SemSoCont qLab: SoContexts qLab -> modelStructure.(Valuations) qLab -> Prop;
      SemSoCompat qLab: forall Sigma r s sigma, 
                            SortingRel (qLab := qLab) Sigma r s
                            -> SemSoCont Sigma sigma
                            -> SemSorts s (SemTerms sigma r);

      SemAtom : forall a:DPair Atom,
                STList modelStructure (ex1 a)
                -> modelStructure.(SLab) -> Prop;

      SemAtom_eq qLab sigma: 
        forall a b p, is_eq a b
                 -> Pard (qLab := qLab) (@SemAtom) sigma a p -> Pard (@SemAtom) sigma b p

    }.

  Global Arguments SemAtom {_} a _ _.

  (* We now assume we have a realisability algebra *)

  Variable M: RealisabilityAlg.

  (* Here is the orthogonal of a set of positive elements of the model, or more precisely a predicate P: M.(positive) -> Prop *)
  Definition ortho P tm :=
    forall tp: M.(SPos), P tp -> orth (tm,tp).

  (* Given a molecule A, this is a predicate on positives, that holds if
this positive is of the form (M.(tild) p v), for some pattern p and
some SDec v such that p decomposes A into some TypeTree Delta and v is
in the semantics of Delta. The semantics of TypeTrees not being defined
yet, it is passed as an argument SemContext.  *)

  Unset Implicit Arguments.

  Inductive PV
            (A: DPair Molecule)
            (SemTDec: forall st, TypingDec st (ex1 A)
                               -> forall tl:STList M (ex1 A), SDec st -> Prop)
            (tl: STList M (ex1 A))
  : M.(SPos) -> Prop :=
    pv : forall p Delta v,
           PatternsTyped p Delta (ex2 A)
           -> SemTDec (PatDec p) Delta tl v 
           -> PV A SemTDec tl (tild p v).

  (* The interpretation (predicate on SDecs) of a TypeTree Delta, given
a valuation sigma and a function f that provides the negative
interpretation of any molecule B in Delta *)

  Definition SemTDec_aux
             (f : forall (A:DPair (@Molecule LAF)), STList M (ex1 A) -> M.(SNeg) -> Prop)
             l
             st
             (Delta : TypingDec (QST := LAF) st l)
             (tl:STList M l)
             (v: @SDec M st)
  : Prop.
    move : l tl Delta.
    induction st => l tl Delta; inversion Delta; inversion v.
    exact (SemAtom {{ l, X }} tl X0).
    exact (f {{ l, X }} tl X0).
    exact True.
    exact (IHst1 X1 l tl X /\ IHst2 X2 l tl X0).
    exact (SemSorts so X0 /\ IHst X1 (so::l) (TermCons so X0 tl) X).
  Defined.


  (* The positive interpretation (predicate on positives) of a molecule
A, given a valuation sigma that provides the positive interpretation of
every molecule variable, and a function f that already provides the
positive interpretation of any molecule B smaller than A *)

  Definition SemPos_aux
             (A: DPair Molecule)
             (f : forall B, relation B A -> STList M (ex1 B) -> M.(SPos) -> Prop)
    := PV A (SemTDec_aux (fun B tl tm => exists h:relation B A, ortho (f B h tl) tm) (ex1 A)).

  (* The positive interpretation (predicate on positives) of a molecule
A, given a type valuation sigma. Fixpoint of the previous function, built on
the well-founded relation on molecules. *)

  Definition SemPos := Fix M.(welf) _ (SemPos_aux).

  (* The negative interpretation (predicate on negatives) of a molecule
A, given a valuation sigma. It is built as the orthogonal of the positive
interpretation of A.  *)

  Definition SemNeg A tl := ortho (SemPos A tl).

  (* A new version of the interpretation (predicate on SDecs) of a
TypeTree Delta, given a valuation sigma, but this time the predicate
used as the negative interpretation of any molecule B in Delta is not
passed as a parameter, it is the actual interpretation SemNeg *)

  Definition SemTDec {l st} := SemTDec_aux (@SemNeg) l st.

  (* The definition of SemPos is so far quite cryptic, because of the
induction that was necessary for the definition to be sound. The
theorem below characterise SemPos in a much more intuitive way, but
before that we need the following two lemmas. *)

  Lemma F_ext_aux:
    forall (x:DPair Molecule)
      (f g: forall y:DPair Molecule, 
              relation y x -> STList M (ex1 y) -> M.(SPos) -> Prop),
      (forall (y:DPair Molecule) (p:relation y x) tl d, f y p tl d <-> g y p tl d) 
      -> forall st l (Delta:TypingDec st l),
          forall tl' (v : SDec st),
            SemTDec_aux (fun (B : DPair Molecule) tl (tm : M.(SNeg)) =>
                           exists h : relation B x, ortho (f B h tl) tm)
                        _ _ Delta tl' v ->
            SemTDec_aux (fun (B : DPair Molecule) tl (tm : M.(SNeg)) =>
                           exists h : relation B x, ortho (g B h tl) tm)
                        _ _ Delta tl' v .
  Proof.
    move => A f g H st.

    induction st;
      dependent induction v;
      dependent induction Delta => //;simpl.

    unfold ortho.
    elim => h H1.
    exists h.
    move => // tp H2.
    apply: H1.
    by apply H.

    case => H1 H2.
    by split; [apply: IHst1 |apply: IHst2].

    clear  IHv.
    move => [H1 H2].
    split =>//.
    by apply IHst.
  Qed.

  Lemma F_ext :
    forall (x:DPair Molecule)
      (f g: forall y:DPair Molecule, 
              relation y x -> STList M (ex1 y) -> M.(SPos) -> Prop),
      (forall (y:DPair Molecule) (p:relation y x) tl d, f y p tl d <-> g y p tl d) 
      -> forall tl d, SemPos_aux x f tl d -> SemPos_aux x g tl d.
  Proof.
    move => A f g H tl d.
    unfold SemPos_aux.
    elim.
    intros.
    apply (pv A _ tl p Delta v) => //.
    move : v H1 ; clear H0 d.
    apply F_ext_aux =>//. 
  Qed.

  Lemma Fix_F_inv :
    forall (x:DPair Molecule) tl d (r s:Acc relation x),
      Fix_F (fun A => STList M (ex1 A) -> M.(SPos) -> Prop) 
            SemPos_aux r tl d 
      <-> 
      Fix_F (fun A => STList M (ex1 A) -> M.(SPos) -> Prop)
            SemPos_aux s tl d.
  Proof.
    move => A; induction (M.(welf) A).
    move => tl d r s.
    rewrite <- (Fix_F_eq _ _ r). 
    rewrite <- (Fix_F_eq _ _ s).
    split.
    apply (@F_ext _ 
                 (fun (y : DPair Molecule) (p : relation y x)  =>
                    Fix_F _ (@SemPos_aux) (Acc_inv r p))) => //=.
    auto.
    apply (@F_ext _
                 (fun (y : DPair Molecule) (p : relation y x)  =>
                    Fix_F _ (@SemPos_aux) (Acc_inv s p))) => //=.
    auto.
  Qed.

  (* Characterisation of SemPos: The first step is to have a
reformulation that looks much more like the definition of SemPos_aux,
but with the actual SemPos taking the place of the parameter f *)

  Lemma SemPos_Fix :
    forall A tl tp, 
      SemPos A tl tp 
      <-> PV A 
           (SemTDec_aux (fun B tl' tm => exists h:relation B A, ortho (SemPos B tl') tm) (ex1 A))
           tl
           tp.
  Proof.
    move => A tl tp; unfold SemPos; unfold Fix in |- *.
    rewrite <- Fix_F_eq.
    split; apply F_ext; intros; apply Fix_F_inv.
  Qed.

  (* Characterisation of SemPos: The second step is to have a
reformulation which drops the requirement B smaller than A in its use
of SemTDec_aux (that requirement was needed for the well-foundedness
of the definition of SemPos) *)

  Lemma SemPosDec_aux1 : 
    forall A st l (Delta:TypingDec st l) tl (v:SDec st), 
      (forall B : DPair Molecule, belong Delta (ex2 B) -> relation B A)
      -> SemTDec_aux (fun (B : DPair Molecule) tl' (tm : M.(SNeg)) => 
                       ortho (SemPos B tl') tm) 
                    l st Delta tl v      
      -> SemTDec_aux (fun (B : DPair Molecule) tl' (tm : M.(SNeg)) =>
                       exists _ : relation B A, ortho (SemPos B tl') tm)
                    l st Delta tl v.
  Proof.
    move => A.
    induction st;
      dependent induction Delta ; move => tl v; 
      dependent induction v => H //; simpl.

      + move => H1.
        assert (belong (TleafN m) m).
        apply rel_leaf.
        assert (relation (existS _ l m) A).
        apply H => //=.
        by exists H2.
      + clear IHDelta1 IHDelta2 IHv1 IHv2.
        elim => H3 H4.
        split.
        * apply IHst1 => //.
          move => B H5.
          apply: H.
          apply: rel_node1 => //.
        * apply: IHst2 => //.
          move => B H5.
          apply: H.
          apply: rel_node2 => //.
    + clear IHDelta IHv.
        move => [H1 H2].
        split =>//.
        apply: IHst => //.
        move => B H5.
        apply: H.
        apply: rel_nodeq => //.
    Qed.

  Lemma SemPosDec_aux2: 
    forall A st l (Delta:TypingDec st l) tl (v:SDec st), 
      SemTDec_aux (fun (B : DPair Molecule) tl' (tm : M.(SNeg)) =>
                       exists _ : relation B A, ortho (SemPos B tl') tm)
                    l st Delta tl v
      -> SemTDec_aux (fun (B : DPair Molecule) tl' (tm : M.(SNeg)) =>
                       ortho (SemPos B tl') tm) 
                    l st Delta tl v.
  Proof.
    move => A.
    induction st;
      dependent induction Delta ; move => tl v; 
      dependent induction v => //; simpl.
    + by move => [_ H] //=.
    + by elim => H3 H4; split; [ apply IHst1 | apply IHst2].
    + by move => [H4 H]; split => //; apply: IHst.
    Qed.

  Lemma SemPosDec_aux: 
    forall A tl tp, 
      PV A 
         (SemTDec_aux (fun B tl' tm => ortho (SemPos B tl') tm) (ex1 A))
         tl
         tp      
      <-> PV A 
           (SemTDec_aux (fun B tl' tm => exists h:relation B A, ortho (SemPos B tl') tm) (ex1 A))
           tl
           tp.
  Proof.
    elim => lA Araw.
    intros.
    split => H;elim H;clear H;intros; apply (pv {{ lA,Araw }} _ tl p Delta v) => //=.
    + assert  (forall (B : DPair Molecule),
                 belong Delta (ex2 B) -> relation B {{ lA,Araw }}).
        * elim => lB Braw.
          intros.
          apply (relation_base p Delta) => //=.
      apply SemPosDec_aux1 =>//.
      apply (SemPosDec_aux2 {{ lA,Araw }}) =>//.
  Qed.


  (* Characterisation of SemPos: the final step is to write the
definition we would actually like, and notice that, when unfolded, it
is equivalent to the actual definition by using the previous two
lemmas *)

  Theorem SemPosDec : forall A tl tp, SemPos A tl tp <-> PV A (@SemTDec (ex1 A)) tl tp.
  Proof.
    intros;split; intro.
    apply SemPosDec_aux;apply SemPos_Fix => //=.
    apply SemPos_Fix;apply SemPosDec_aux => //=.
  Qed.

  (* We define the interpretation of a typing context as a predicate on
semantic contexts *)

  Definition SemCont {w}: TContext w -> M.(SContexts) w -> Prop
    := fun Gamma rho =>
      SemSoCont (TreadE Gamma) (readE rho)
      /\ (forall xp, (Pard SemAtom (readE rho)) (Treadp Gamma xp) (readp rho xp))
      /\ (forall xn, (Pard SemNeg (readE rho)) (Treadn Gamma xn) (readn rho xn)).

End TypeSemantics.

Arguments SemAtom {_} _ _ _.
Arguments SemPos {M} _ _ _.
Arguments SemTDec {M l st} _ _ _.
Arguments SemNeg {M} _ _ _.
Arguments SemCont {M w} _ _.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

(**************************************)

Section Adequacy.
  
  (* Even though we don't need to formalise a notion of reduction for
proof-terms, the Adequacy Lemma requires from a model that its
orthogonality relation be closed "under anti-reduction" *)

  Record FullModel := 
    {
      M0 :> RealisabilityAlg;

      TypingCorr w st :
        forall (rho:M0.(SContexts) w) Gamma l (Delta:TypingDec st l) tl v, 
          SemCont Gamma rho
          -> SemTDec Delta (SemTermList (readE rho) tl) v
          -> SemCont (Textends [Delta,tl] Gamma) (extends v rho);

      Stability w :
        forall (f: Reifiable w) (rho: M0.(SContexts) w) (p: Patterns LAF)
          l Delta (tl:STList M0 l) (v: SDec (PatDec p)) c,
          f p =cis= c
          -> SemTDec Delta tl v
          -> orth (SemC (extends v rho) c)
          -> orth (I rho f, tild p v)
    }.

  (* Here is finally the Adequacy Lemma *)

  Theorem adequacy (M:FullModel) :
    forall (w:World LAF) (Gamma:TContext w),
      (forall pt A,
         PosTyping Gamma pt A
         ->  forall rho:M.(SContexts) w, SemCont Gamma rho
                 -> Pard SemPos (readE rho) A (SemP rho pt)
      )
      /\ (forall l st (v:TermDec st) Delta tl,
           DecTyping Gamma v Delta tl
           ->  forall rho:M.(SContexts) w, SemCont Gamma rho
                   -> SemTDec (l:=l) Delta (SemTermList (readE rho) tl) (SemDec rho v)
        )
      /\ (forall nt A,
           NegTyping Gamma nt A
           ->  forall rho:M.(SContexts) w, SemCont Gamma rho
                   -> Pard SemNeg (readE rho) A (SemN rho nt)
        )
      /\ (forall c,
           OptionCommandTyping Gamma c
           ->  forall rho:M.(SContexts) w, SemCont Gamma rho
                   -> exists csem, (SemOptionC rho c) = Some csem /\ orth csem)
      /\ (forall c,
           CommandTyping Gamma c
           ->  forall rho:M.(SContexts) w, SemCont Gamma rho
                   -> orth (SemC rho c))
  .
  Proof.

    apply typing_ind;intros;
    [
      (* Typing a positive *)
      apply SemPosDec; by apply (pv _ {{l, A}} _ _ p Delta) =>//; apply (H rho H0)

      (* Typing a positive leaf of Sub *)
      | unfold SemTDec => //= ;
        by apply (SemAtom_eq i) => //;
        elim: H => _ [H _]; apply:H

      (* Typing a negative leaf of Sub *)
      | unfold SemTDec => //= ; by apply H

      (* Typing a dummy leaf of Sub *)
      | unfold SemTDec => //= 

      (* Typing a node of Sub *)
      | by unfold SemTDec => //=; unfold SemTDec in H, H0; split; [apply H|apply H0]

      (* Typing a qnode of Sub *)
      | unfold SemTDec => //=; 
        by split;
           [ apply (SemSoCompat (Sigma:=TreadE Gamma)); move:H0;rewrite/SemCont;elim => H2 _ 
           | apply H ]

      (* Typing a negative *)
      | 

      (* Typing an optional command *)
      | by exists (SemC rho c); split; [| apply: H]

      (* Typing a cut *)
      | by rewrite /SemTDec/Pard/SemNeg/ortho/getA/getTerms in H;apply H =>//; apply H0

      (* Typing a select *)
      | by rewrite /SemC/SemCont/Pard/SemNeg/ortho in H0;apply H0;apply H
    ].

    (* Typing a negative *)
    rewrite /Pard/SemNeg/ortho/getA/getTerms => /= tp H1.
    assert (PV M {{ l,A }} (@SemTDec M l) (SemTermList (readE rho) tl) tp)
      by apply SemPosDec =>//=.
    elim H2 => /= p Delta v H3 H4; clear H2.
    have H6: (exists csem : SNeg M * SPos M,
                SemOptionC (extends v rho) (f p) = Some csem
                /\ orth csem).
    apply: (H p Delta) => //.
    apply: TypingCorr => //.
    elim: H6 => csem [H7 H8].
    have : exists c, (f p = some c).
    move : H7.
    elim (f p) =>/=.
    by move => c _; exists c.
    move => H9;discriminate H9.
    elim => c H9.
    apply (Stability (Delta := Delta) (tl := (SemTermList (readE rho) tl)) (c := c)) => //.
    by rewrite H9.
    move:H7.
    rewrite H9 => /= H7; injection H7; clear H7 => H7; rewrite H7 =>//.
  Qed.

End Adequacy.

Print Assumptions adequacy.

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
