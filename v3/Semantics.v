Require Import ssreflect Basic SyntaxTyping List Coq.Program.Equality.

(* We now define the semantics of terms according to a FullModelRaw *)
Section TermSemantics.

  (* A model has four support sets: terms, primitives, positives and negatives, and a
relation ortho between negatives and positives *)
  
  Record Model4PTermsRaw := {
                      terms      : Type;
                      primitives : Type;
                      positives  : Type;
                      negatives  : Type;
                      orth: negatives*positives -> Prop
                    }
  .

  (* We first define semantical trees, which will interpret termtrees *)

  Definition SemTree {M} := @Tree M.(terms) M.(primitives) M.(negatives).

  (* This is a useful abbreviation for type valuations *)

  Definition qvaluation {M} qVar := qVar -> M.(terms).

  (* In order to build a model of proof-terms, we require an
interpretation of terms, 
an interpretation of patterns, 
and an interpretation of the reifeied functions *)

  Record Model4PTerms := 
    {
      model :> Model4PTermsRaw;

      SemTerms {QVar}: @qvaluation model QVar -> Term QVar -> model.(terms);

      SemTermsRen {QVar QVar'}:
        forall (ren:QVar -> QVar') (sigma:@qvaluation model QVar) tau,
          (forall xq, tau (ren xq) = sigma xq)
          -> forall t, SemTerms sigma t = SemTerms tau (Term.(qrename) ren t);

      SemTermsVar {QVar} sigma (xq:QVar): SemTerms sigma (Term.(varTerm) xq) = sigma xq;

      tild : forall p:Patterns, @SemTree model (PatTree p) -> model.(positives);

      I {w} : @ContType model.(terms) model.(primitives) model.(negatives) w
              -> @Reifiable w
              -> model.(negatives)
    }.

  Variable M: Model4PTerms.

  Fixpoint SemTermList {qVar} sigma {P l} (tl:@TermList (Term qVar) P l)
  :UTTermList M.(terms) l
    := match tl with
        | TermNil => TermNil
        | TermCons r so H l' tl' => TermCons (M.(SemTerms) sigma r) Logic.I (SemTermList sigma tl')
      end.

  Lemma SemTermListRen {QVar QVar'}:
        forall (ren:QVar -> QVar') (sigma:@qvaluation M QVar) tau,
          (forall xq, tau (ren xq) = sigma xq)
          -> forall l tl, SemTermList (l := l) sigma tl = SemTermList tau (UTTermListRen ren tl).
  Proof.
    intros.
    induction l.
    dependent inversion tl =>//.
    dependent inversion tl =>//=.
    rewrite (M.(SemTermsRen) (QVar := QVar) (QVar' := QVar') ren sigma tau) =>//.
    by rewrite IHl.
  Qed.

  (* We apply our implementation of contexts to the notion of semantic
contexts (aka valuations): positive (resp. negative) variables are
mapped to positive (resp. negative) elements of the model *)
  Definition SContext := @ContType M.(terms) M.(primitives) M.(negatives).

  (* The semantics of a negative term is a negative element of the model *)
  Definition SemN {w} (rho:SContext w) (tm : Neg) := 
    match tm with
      | rei f => M.(I) rho f
    end
  .

  (* The semantics of a TermTree is a SemTree *)
  Fixpoint SemSub {w} (rho:SContext w) {st} (v : TermTree st) {struct v} :=
    match v in @TermTree _ s return SemTree s with
      | tleafP xp => leafP (rho.(readp) xp)
      | tleafN tm => leafN (SemN rho tm)
      | tdummy    => dummy
      | tnode s1 s2 v1 v2 => node (SemSub rho (st:=s1) v1) (SemSub rho (st:=s2) v2)
      | tqnode s r v => qnode (M.(SemTerms) rho.(readq) r) (SemSub rho (st:=s) v)
    end
  .

  (* The semantics of a positive term is a positive element of the model *)
  Definition SemP {w} (rho:SContext w) (pt : Pos) := 
    match pt with
        pos p v => M.(tild) p (SemSub rho v)
    end
  .

  (* The semantics of a command is a pair (negative element,positive
element) of the model, that may or may not be orthogonal *) 

  Definition SemC {w} (rho:SContext w) (c : Command) :=
    match c with
      | cut tm tp => (SemN rho tm,SemP rho tp) 
      | select xm tp => (rho.(readn) xm,SemP rho tp)
    end 
  .

  Definition SemOptionC {w} (rho:SContext w)(oc : OptionCommand) :=
    match oc with
      | some c => Some(SemC (rho:SContext w) c)
      | none => None
    end
  .

End TermSemantics.




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

Inductive  belong {l}
: forall l' st, TypeTree st l' -> Molecule l -> Prop
  :=
  | rel_leaf  : forall B, belong l sleafN (TleafN B) B
  | rel_node1 : forall B l' s1 s2 t1 t2,
                  belong l' s1 t1 B -> belong l' (snode s1 s2) (Tnode t1 t2) B
  | rel_node2 : forall B l' s1 s2 t1 t2,  
                  belong l' s2 t2 B -> belong l' (snode s1 s2) (Tnode t1 t2) B
  | rel_nodeq : forall so B l' s t, 
                  belong (so::l') s t B
                  -> belong l' (sqnode s) (Tqnode so t) B
.

Inductive relation : DPair Molecule -> DPair Molecule -> Prop :=
  relation_base:
    forall p l l' Delta A B, PatternsTyped p Delta A
               -> belong l' (PatTree p) Delta B
               -> relation (existS _ l B) (existS _ l' A).

Hypothesis welf: well_founded relation.


(****************************************************************)
(* We now define the semantics of types according to a ModelRaw *)

Section TypeSemantics.

  Definition Pard {A B} {M:Model4PTerms} 
             (f: forall a:DPair A, UTTermList (terms M) (ex1 a) -> B)
             {qVar} sigma a
    := f {{ ex1 a, getA (qVar := qVar) a }} (SemTermList M sigma (getTerms a)).
  
  Record ModelRaw :=
    { model4PTerms :> Model4PTerms;
      sortsI: Sorts -> model4PTerms.(terms) -> Prop;
      sortscompat {qVar}: forall Sigma sigma,
                            (forall qvar:qVar, sortsI (Sigma qvar) (sigma qvar))
                            -> forall s t, 
                                SortingRel Sigma t s
                                -> sortsI s (model4PTerms.(SemTerms) sigma t);

      atomI : forall a:DPair Atom,
                UTTermList model4PTerms.(terms) (ex1 a)
                -> model4PTerms.(primitives) -> Prop;

      atomI_eq {qVar sigma}: forall a b p, is_eq a b
                                  -> Pard (qVar := qVar) atomI sigma a p -> Pard atomI sigma b p

    }.

  Variable M: ModelRaw.

  (* Here is the orthogonal of a set of positive elements of the model, or more precisely a predicate P: M.(positive) -> Prop *)
  Definition ortho P :=
    fun tm => forall tp: M.(positives), P tp -> M.(orth) (tm,tp).

  (* Given a molecule A, this is a predicate on positives, that holds if
this positive is of the form (M.(tild) p v), for some pattern p and
some SemTree v such that p decomposes A into some TypeTree Delta and v is
in the semantics of Delta. The semantics of TypeTrees not being defined
yet, it is passed as an argument SemContext.  *)

  Inductive PV
            (A: DPair Molecule)
            (SemContext: forall st, TypeTree st (ex1 A)
                               -> forall tl:UTTermList M.(terms) (ex1 A), SemTree st -> Prop)
            (tl: UTTermList M.(terms) (ex1 A))
  : M.(positives) -> Prop :=
    pv : forall p Delta v,
           PatternsTyped p Delta (ex2 A)
           -> SemContext (PatTree p) Delta tl v 
           -> PV A SemContext tl (M.(tild) p v).

  (* The interpretation (predicate on SemTrees) of a TypeTree Delta, given
a valuation sigma and a function f that provides the negative
interpretation of any molecule B in Delta *)

  Definition SemCont_aux
             (f : forall (A:DPair Molecule), UTTermList M.(terms) (ex1 A) -> M.(negatives) -> Prop)
             l
             st
             (Delta : TypeTree st l)
             (tl:UTTermList M.(terms) l)
             (v: @SemTree M st)
  : Prop.
    move : l tl Delta.
    induction st => l tl Delta; inversion Delta; inversion v.
    exact (M.(atomI) {{ l, X }} tl X0).
    exact (f {{ l, X }} tl X0).
    exact True.
    exact (IHst1 X1 l tl X /\ IHst2 X2 l tl X0).
    exact ( M.(sortsI) so X0 /\ IHst X1 (so::l) (TermCons X0 (Logic.I) tl) X).
  Defined.


  (* The positive interpretation (predicate on positives) of a molecule
A, given a valuation sigma that provides the positive interpretation of
every molecule variable, and a function f that already provides the
positive interpretation of any molecule B smaller than A *)

  Definition SemPos_aux
             (A: DPair Molecule)
             (f : forall B, relation B A -> UTTermList M.(terms) (ex1 B) -> M.(positives) -> Prop)
    := PV A (SemCont_aux (fun B tl tm => exists h:relation B A, ortho (f B h tl) tm) (ex1 A)).

  (* The positive interpretation (predicate on positives) of a molecule
A, given a type valuation sigma. Fixpoint of the previous function, built on
the well-founded relation on molecules. *)

  Definition SemPos := Fix welf _ (SemPos_aux).

  (* The negative interpretation (predicate on negatives) of a molecule
A, given a valuation sigma. It is built as the orthogonal of the positive
interpretation of A.  *)

  Definition SemNeg A tl := ortho (SemPos A tl).

  (* A new version of the interpretation (predicate on SemTrees) of a
TypeTree Delta, given a valuation sigma, but this time the predicate
used as the negative interpretation of any molecule B in Delta is not
passed as a parameter, it is the actual interpretation SemNeg *)

  Definition SemCont {l st} := SemCont_aux SemNeg l st.

  (* The definition of SemPos is so far quite cryptic, because of the
induction that was necessary for the definition to be sound. The
theorem below characterise SemPos in a much more intuitive way, but
before that we need the following two lemmas. *)

  Lemma F_ext_aux:
    forall (x:DPair Molecule)
      (f g: forall y:DPair Molecule, 
              relation y x -> UTTermList M.(terms) (ex1 y) -> M.(positives) -> Prop),
      (forall (y:DPair Molecule) (p:relation y x) tl d, f y p tl d <-> g y p tl d) 
      -> forall st l (Delta:TypeTree st l),
          forall tl' (v : SemTree st),
            SemCont_aux (fun (B : DPair Molecule) tl (tm : negatives M) =>
                           exists h : relation B x, ortho (f B h tl) tm)
                        l st Delta tl' v ->
            SemCont_aux (fun (B : DPair Molecule) tl (tm : negatives M) =>
                           exists h : relation B x, ortho (g B h tl) tm)
                        l st Delta tl' v .
  Proof.
    move => A f g H st.

    induction st;
      dependent induction v;
      dependent induction Delta => //;simpl.

    unfold ortho.
    elim => h H1.
    exists h.
    move => tp H2.
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
              relation y x -> UTTermList M.(terms) (ex1 y) -> M.(positives) -> Prop),
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
      Fix_F (fun A => UTTermList (terms M) (ex1 A) -> M.(positives) -> Prop) 
            SemPos_aux r tl d 
      <-> 
      Fix_F (fun A => UTTermList (terms M) (ex1 A) -> M.(positives) -> Prop)
            SemPos_aux s tl d.
  Proof.
    move => A; induction (welf A).
    move => tl d r s.
    rewrite <- (Fix_F_eq _ _ r). 
    rewrite <- (Fix_F_eq _ _ s).
    split.
    apply (F_ext _
                 (fun (y : DPair Molecule) (p : relation y x)  =>
                    Fix_F _ SemPos_aux (Acc_inv r p))) => //=.
    auto.
    apply (F_ext _
                 (fun (y : DPair Molecule) (p : relation y x)  =>
                    Fix_F _ SemPos_aux (Acc_inv s p))) => //=.
    auto.
  Qed.

  (* Characterisation of SemPos: The first step is to have a
reformulation that looks much more like the definition of SemPos_aux,
but with the actual SemPos taking the place of the parameter f *)

  Lemma SemPos_Fix :
    forall A tl tp, 
      SemPos A tl tp 
      <-> PV A 
           (SemCont_aux (fun B tl' tm => exists h:relation B A, ortho (SemPos B tl') tm) (ex1 A))
           tl
           tp.
  Proof.
    move => A tl tp; unfold SemPos; unfold Fix in |- *.
    rewrite <- Fix_F_eq.
    split; apply F_ext; intros; apply Fix_F_inv.
  Qed.

  (* Characterisation of SemPos: The second step is to have a
reformulation which drops the requirement B smaller than A in its use
of SemCont_aux (that requirement was needed for the well-foundedness
of the definition of SemPos) *)

  Lemma SemPosCont_aux1 : 
    forall A st l (Delta:TypeTree st l) tl (v:SemTree st), 
      (forall B : DPair Molecule, belong l st Delta (ex2 B) -> relation B A)
      -> SemCont_aux (fun (B : DPair Molecule) tl' (tm : negatives M) => 
                       ortho (SemPos B tl') tm) 
                    l st Delta tl v      
      -> SemCont_aux (fun (B : DPair Molecule) tl' (tm : negatives M) =>
                       exists _ : relation B A, ortho (SemPos B tl') tm)
                    l st Delta tl v.
  Proof.
    move => A.
    induction st;
      dependent induction Delta ; move => tl v; 
      dependent induction v => H //; simpl.

      + move => H1.
        assert (belong _ sleafN (TleafN m) m).
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

  Lemma SemPosCont_aux2: 
    forall A st l (Delta:TypeTree st l) tl (v:SemTree st), 
      SemCont_aux (fun (B : DPair Molecule) tl' (tm : negatives M) =>
                       exists _ : relation B A, ortho (SemPos B tl') tm)
                    l st Delta tl v
      -> SemCont_aux (fun (B : DPair Molecule) tl' (tm : negatives M) =>
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

  Lemma SemPosCont_aux: 
    forall A tl tp, 
      PV A 
         (SemCont_aux (fun B tl' tm => ortho (SemPos B tl') tm) (ex1 A))
         tl
         tp      
      <-> PV A 
           (SemCont_aux (fun B tl' tm => exists h:relation B A, ortho (SemPos B tl') tm) (ex1 A))
           tl
           tp.
  Proof.
    elim => lA Araw.
    intros.
    split => H;elim H;clear H;intros; apply (pv {{ lA,Araw }} _ tl p Delta v) => //=.
    + assert  (forall (B : DPair Molecule),
                 belong lA (PatTree p) Delta (ex2 B) -> relation B {{ lA,Araw }}).
        * elim => lB Braw.
          intros.
          apply (relation_base p lB lA Delta) => //=.
      apply SemPosCont_aux1 =>//.
      apply (SemPosCont_aux2 {{ lA,Araw }}) =>//.
  Qed.


  (* Characterisation of SemPos: the final step is to write the
definition we would actually like, and notice that, when unfolded, it
is equivalent to the actual definition by using the previous two
lemmas *)

  Theorem SemPosCont : forall A tl tp, SemPos A tl tp <-> PV A (@SemCont (ex1 A)) tl tp.
  Proof.
    intros;split; intro.
    apply SemPosCont_aux;apply SemPos_Fix => //=.
    apply SemPos_Fix;apply SemPosCont_aux => //=.
  Qed.

End TypeSemantics.

Arguments SemPos {M} _ _ _.
Arguments SemCont {M} {l st} _ _ _.
Arguments SemNeg {M} _ _ _.
Arguments atomI {m} _ _ _.

(**************************************)

Section Adequacy.
  
  (* Even though we don't need to formalise a notion of reduction for
proof-terms, the Adequacy Lemma requires from a model that its
orthogonality relation be closed "under anti-reduction" *)

  Record FullModel := 
    {
      M0 :> ModelRaw;

      treevalue {st}: @SemTree M0 st -> Prop;

      stab {w} :
        forall (f: Reifiable) (rho: SContext M0 w) (p: Patterns) (v: SemTree (PatTree p)) c,
          treevalue v
          -> f p =cis= c
          -> M0.(orth) (SemC M0 (Context.(extends) v rho) c)
          -> M0.(orth) (M0.(I) rho f, M0.(tild) p v)
    }.

  Variable M:FullModel.

  (* We define the interpretation of a typing context as a predicate on
semantic contexts *)

  Definition compat {w w'} val: @ContType Sorts 
                                  (Par Atom w'.(QVar))
                                  (Par Molecule w'.(QVar))
                                  w
                             -> SContext M w -> Prop
    := Contlift (w := w) M.(sortsI)(Pard atomI val) (Pard SemNeg val).

  Lemma SemPos2Treelift  qVar qVar' (sigma:qvaluation qVar) (tau:qvaluation qVar') (ren:qVar -> qVar') st qnew l Delta (tl:UTTermList M.(terms) l) tl' v 
  :  (forall xq, tau (ren xq) = sigma xq)
     -> correctNaming tau v qnew
     -> tl = SemTermList M tau tl'
     -> SemCont (M := M)(st := st) Delta tl v
     -> Treelift M.(sortsI) (Pard atomI tau) (Pard SemNeg tau) (namedTypeTree tl' Delta qnew) v.

  Proof.
    move : l Delta tl tl'.
    induction st => l Delta tl tl' H0 H1  H2; dependent induction v =>//=; dependent induction Delta =>//=; dependent induction qnew =>//=.
    rewrite /getA/getTerms/ex2. 
    by rewrite H2.
    rewrite /getA/getTerms/ex2. 
    by rewrite H2.
    simpl in H1. 
    elim: H1 => H3 H4.
    move => [I1 I2]; split ; [apply (IHst1 _ _ _ _ tl) | apply (IHst2 _ _ _ _ tl) ] =>//.
    simpl in H1. 
    elim: H1 => H3 H4.
    elim => H5 H6; split => //.
    clear IHv IHDelta IHqnew.
    apply (IHst _ _ _ _ (TermCons c Logic.I tl)) =>//.
    simpl.
    by rewrite SemTermsVar H3 H2.
Qed.

  Lemma compatrename w w' Gamma rho sigma tau (ren:w.(QVar) -> w'.(QVar))
  (pi: forall xq, tau (ren xq) = sigma xq)
  : compat sigma Gamma rho -> compat tau (Contmap (w:=w) (fun i => i) (ParRen ren) (ParRen ren) Gamma) rho.
  Proof.
    rewrite/compat/Contlift/Contmap;elim => H1 [H2 H3] /=.
                                              split => //;split.
    move => xp.
    move: (H2 xp); clear H2 H3.
    elim : (readp Gamma xp) => l [a tl]. 
    rewrite /Pard/ParRen/ex1/getA/getTerms/ex2; simpl.
    rewrite (SemTermListRen (QVar := w.(QVar)) (QVar' := w'.(QVar)) M ren sigma tau) =>//.
    move => xn.
    move: (H3 xn); clear H2 H3.
    elim : (readn Gamma xn) => l [a tl]. 
    rewrite /Pard/ParRen/ex1/getA/getTerms/ex2; simpl.
    rewrite (SemTermListRen (QVar := w.(QVar)) (QVar' := w'.(QVar)) M ren sigma tau) =>//.
Qed.

  (* Here is finally the Adequacy Lemma *)

  Hypothesis HValues: forall st (v:SemTree st) l Delta tl, SemCont (l := l) Delta tl v -> treevalue M v.

  Theorem adequacy:
    forall (w:World) (Gamma:TContext w),
      (forall pt A,
         TypingPos Gamma pt A
         ->  forall rho, compat rho.(readq) Gamma rho
                 -> Pard SemPos rho.(readq) A (SemP M rho pt)
      )
      /\ (forall l st (v:TermTree st) Delta tl,
           TypingSub Gamma v Delta tl
           ->  forall rho, compat rho.(readq) Gamma rho
                   -> SemCont (l:=l) Delta (SemTermList M rho.(readq) tl) (SemSub M rho v)
        )
      /\ (forall nt A,
           TypingNeg Gamma nt A
           ->  forall rho, compat rho.(readq) Gamma rho
                   -> Pard SemNeg rho.(readq) A (SemN M rho nt)
        )
      /\ (forall c,
           TypingOptionCommand Gamma c
           ->  forall rho, compat rho.(readq) Gamma rho
                   -> exists csem, (SemOptionC M rho c) = Some csem /\ M.(orth) csem)
      /\ (forall c,
           TypingCommand Gamma c
           ->  forall rho, compat rho.(readq) Gamma rho
                   -> M.(orth) (SemC M rho c))
  .
    apply typing_ind;intros;
    [
      (* Typing a positive *)
      apply SemPosCont; by apply (pv _ {{l, A}} _ _ p Delta) =>//; apply (H rho H0)

      (* Typing a positive leaf of Sub *)
      | unfold SemCont => //=;
        by apply (M.(atomI_eq) (qVar:= w.(QVar)) (sigma:= rho.(readq)) 
                        (Gamma.(readp) xp) {{l, (x, tl)}}) => //;
        elim: H => _ [H _]; apply:H 

      (* Typing a negative leaf of Sub *)
      | unfold SemCont => //= ; by apply H

      (* Typing a dummy leaf of Sub *)
      | unfold SemCont => //= 

      (* Typing a node of Sub *)
      | by unfold SemCont => //=; unfold SemCont in H, H0; split; [apply H|apply H0]

      (* Typing a qnode of Sub *)
      | unfold SemCont => //=; 
        by split;
           [ apply (sortscompat M (Gamma.(readq))); move:H0;rewrite/compat/Contlift;elim => H2 _ 
           | apply H ]

      (* Typing a negative *)
      | 

      (* Typing an optional command *)
      | by exists (SemC M rho c); split; [| apply: H]

      (* Typing a cut *)
      | by rewrite /SemCont/Pard/SemNeg/ortho/getA/getTerms in H;apply H =>//; apply H0

      (* Typing a select *)
      | by rewrite /SemC/compat/Pard/SemNeg/ortho in H0;apply H0;apply H
    ].
    
    (* Typing a negative *)
    rewrite /Pard/SemNeg/ortho/getA/getTerms => /= tp H1.
    assert (PV M {{ l,A }} (@SemCont M l) (SemTermList M (readq rho) tl) tp)
      by apply SemPosCont =>//=.
    elim H2 => /= p Delta v H3 H4; clear H2.
    have H6: (exists csem : negatives M * positives M,
                SemOptionC (w:=Context.(wextends) (PatTree p) w)
                           M
                           (Context.(extends) v rho)
                           (f p) = Some csem
                /\ orth M csem).
    apply: (H p Delta) => //.
    apply (Context.(corr) (w:=w) (st:=PatTree p)).
    apply (SemPos2Treelift _ _ rho.(readq) _ 
                                         (qinject Context (PatTree p) w)
                                         (PatTree p)
                                         (qnew Context (PatTree p) w)
                                         l Delta 
                                         (SemTermList M rho.(readq) tl) 
                                         (UTTermListRen (qinject Context (PatTree p) w) tl)
          )=> // .
    move => xq.
    apply (Context.(extends_qinject) (w:=w) (st:=PatTree p)).
    apply (Context.(extends_qnew) (w:=w) (st:=PatTree p)).
    apply SemTermListRen.
    move => xq.
    apply (Context.(extends_qinject) (w:=w) (st:=PatTree p)).
    apply (compatrename _ _ _ _ rho.(readq)) => //.
    move => xq.
    apply (Context.(extends_qinject) (w:=w) (st:=PatTree p)).
    elim: H6 => csem [H7 H8].
    have : exists c, (f p = some c).
    move : H7.
    elim (f p) =>/=.
    by move => c _; exists c.
    move => H9;discriminate H9.
    elim => c H9.
    apply (M.(stab) (w:=w) _ _ _ _ c).
    apply (HValues _ _ _ _ _ H4) =>//.
    by rewrite H9.
    move:H7.
    rewrite H9 => /= H7; injection H7; clear H7 => H7; rewrite H7 =>//.
  Qed.

End Adequacy.

Print Assumptions adequacy.