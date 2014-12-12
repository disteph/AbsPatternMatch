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

      SemTermsVar {QVar} sigma (xq:QVar): SemTerms sigma (Term.(varTerm) xq) = sigma xq;

      tild : forall p:Patterns, @SemTree model (PatTree p) -> model.(positives);

      I {w} : @ContType model.(terms) model.(primitives) model.(negatives) w
              -> @Reifiable w
              -> model.(negatives)
    }.

  Variable M: Model4PTerms.

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

Inductive  belong {qVar l}
: forall st, TypeTree qVar st l -> Molecule qVar -> Prop
  :=
  | rel_leaf  : forall B (tl:UTTermList l), belong sleafN (TleafN B) (substTerms tl B)
  | rel_node1 : forall B s1 s2 t1 t2,
                  belong s1 t1 B -> belong (snode s1 s2) (Tnode t1 t2) B
  | rel_node2 : forall B s1 s2 t1 t2,  
                  belong s2 t2 B -> belong (snode s1 s2) (Tnode t1 t2) B
  | rel_nodeq : forall so B s t, 
                  belong (l := so::l) s t B
                  -> belong (sqnode s) (Tqnode so t) B
.

Inductive relation {qVar}
: Molecule qVar -> Molecule qVar -> Prop :=
  relation_base:
    forall p Delta A B, PatternsTyped p Delta A
               -> @belong qVar nil (PatTree p) Delta B
               -> relation B A.

Hypothesis welf: forall {QVar}, well_founded (@relation QVar).


(****************************************************************)
(* We now define the semantics of types according to a ModelRaw *)

Section TypeSemantics.

  (* Fixpoint UTTermList_map2 {A B l l'} (P:A -> B -> Prop)  *)
  (*          (tl:@UTTermList A l) (tl':@UTTermList B l'): Prop *)
  (*   := match tl,tl' with *)
  (*       | TermNil, TermNil => True *)
  (*       | TermCons r _ _ _ tl0, TermCons r' _ _ _ tl0' *)
  (*         => P r r' /\ UTTermList_map2 P tl0 tl0' *)
  (*       | _,_ => False *)
  (*     end. *)

  Fixpoint SemTermList {qVar M} sigma {P l} (tl:@TermList (Term qVar) P l)
    := match tl with
        | TermNil => nil
        | TermCons r so H l' tl' => (M.(SemTerms) sigma r)::(SemTermList sigma tl')
      end.

  Record ModelRaw :=
    { model4PTerms :> Model4PTerms;
      sortsI: Sorts -> model4PTerms.(terms) -> Prop;
      sortscompat {qVar}: forall Sigma sigma,
                            (forall qvar:qVar, sortsI (Sigma qvar) (sigma qvar))
                            -> forall s t, 
                                SortingRel Sigma t s
                                -> sortsI s (model4PTerms.(SemTerms) sigma t);

      atomI {qVar (* l *)} : @qvaluation model4PTerms qVar
                       (* -> @UTTermList model4PTerms.(terms) l *)
                       -> Atom_d qVar nil
                       -> model4PTerms.(primitives) -> Prop;

      (* atomIsubst {qVar so l sigma}: *)
      (*   forall a c tl p, *)
      (*   @atomI qVar (so::l) sigma (TermCons (model4PTerms.(SemTerms) sigma c) Logic.I tl) a p *)
      (*   <-> atomI sigma tl (substTerms1 c a) p; *)

      atomIren {qVar qVar' l} (sigma:qvaluation qVar) (tau:qvaluation qVar') (ren:qVar -> qVar') 
               (tl:UTTermList l) (tl':UTTermList l) q a
      :  (forall xq, tau (ren xq) = sigma xq)
         -> SemTermList sigma tl = SemTermList tau tl'
         -> (atomI sigma (substTerms tl q) a <->
            atomI tau (substTerms tl' (Atom_d.(qrename) ren q)) a)

      (* atomIren : forall qvar qvar' (a:Atom qvar) sigma tau (ren: qvar -> qvar') *)
      (*              (pi: forall xq, tau (ren xq) = sigma xq) *)
      (*              p, *)
      (*              atomI sigma a p <-> atomI tau (Atom.(qrename) ren a) p *)
    }.
 


  Variable M: ModelRaw.

  (* Definition SemSortedlist := SemSortedlistR M M.(sortsI). *)

  Variable qVar:Type.
  Definition compattval Sigma sigma := forall qvar:qVar, M.(sortsI) (Sigma qvar) (sigma qvar).


  (* Here is the orthogonal of a set of positive elements of the model, or more precisely a predicate P: M.(positive) -> Prop *)
  Definition ortho P :=
    fun tm => forall tp: M.(positives), P tp -> M.(orth) (tm,tp).

  (* Given a molecule A, this is a predicate on positives, that holds if
this positive is of the form (M.(tild) p v), for some pattern p and
some SemTree v such that p decomposes A into some TypeTree Delta and v is
in the semantics of Delta. The semantics of TypeTrees not being defined
yet, it is passed as an argument SemContext.  *)

  Inductive PV
            (A: Molecule qVar)
            (SemContext:forall st l, TypeTree qVar st l
                                -> forall tl:@UTTermList (Term qVar) l, SemTree st -> Prop)
  : M.(positives) -> Prop :=
    pv : forall p Delta v,
           PatternsTyped p Delta A
           -> SemContext (PatTree p) nil Delta TermNil v 
           -> PV A SemContext (M.(tild) p v).

  (* The interpretation (predicate on SemTrees) of a TypeTree Delta, given
a valuation sigma and a function f that provides the negative
interpretation of any molecule B in Delta *)

  Definition SemCont_aux (sigma:@qvaluation M qVar)
             (f : forall (A:Molecule qVar), M.(negatives) -> Prop)
             st
             l
             (Delta : TypeTree qVar st l)
             (tl:@UTTermList (Term qVar) l)
             (v: @SemTree M st)
  : Prop.
    move : l tl Delta.
    induction st => l tl Delta; inversion Delta; inversion v.
    exact (M.(atomI) sigma (substTerms tl X) X0).
    exact (f (substTerms tl X) X0).
    exact True.
    exact (IHst1 X1 l tl X /\ IHst2 X2 l tl X0).
    exact ( M.(sortsI) so X0
            /\ exists t, M.(SemTerms) sigma t = X0
                   /\ IHst X1 (so::l) (TermCons t (Logic.I) tl) X).
  Defined.


  (* The positive interpretation (predicate on positives) of a molecule
A, given a valuation sigma that provides the positive interpretation of
every molecule variable, and a function f that already provides the
positive interpretation of any molecule B smaller than A *)

  Definition SemPos_aux sigma
             (A: Molecule qVar)
             (f : forall B, relation B A -> M.(positives) -> Prop)
    := PV A (SemCont_aux sigma (fun B tm => exists h:relation B A, ortho (f B h) tm)).

  (* The positive interpretation (predicate on positives) of a molecule
A, given a type valuation sigma. Fixpoint of the previous function, built on
the well-founded relation on molecules. *)

  Definition SemPos sigma := Fix welf _ (SemPos_aux sigma).

  (* The negative interpretation (predicate on negatives) of a molecule
A, given a valuation sigma. It is built as the orthogonal of the positive
interpretation of A.  *)

  Definition SemNeg sigma A := ortho (SemPos sigma A).

  (* A new version of the interpretation (predicate on SemTrees) of a
TypeTree Delta, given a valuation sigma, but this time the predicate
used as the negative interpretation of any molecule B in Delta is not
passed as a parameter, it is the actual interpretation SemNeg *)

  Definition SemCont sigma {st} := SemCont_aux sigma (SemNeg sigma) st.


  (* The definition of SemPos is so far quite cryptic, because of the
induction that was necessary for the definition to be sound. The
theorem below characterise SemPos in a much more intuitive way, but
before that we need the following two lemmas. *)

  Lemma F_ext_aux (sigma:@qvaluation M qVar):
    forall (x:Molecule qVar)
      (f g: forall y:Molecule qVar, relation y x -> M.(positives) -> Prop),
      (forall (y:Molecule qVar) (p:relation y x) d,
         f y p d <-> g y p d) 
      -> forall st l (Delta:TypeTree qVar st l),
          forall tl' (v : SemTree st),
            SemCont_aux sigma (fun (B : Molecule qVar) (tm : negatives M) =>
                                exists h : relation B x, ortho (f B h) tm)
                        st l Delta tl' v ->
            SemCont_aux sigma (fun (B : Molecule qVar) (tm : negatives M) =>
                                exists h : relation B x, ortho (g B h) tm)
                        st l Delta tl' v .
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
    elim => H0 [i [H1 H2]].
    split =>//.
    exists i.
    split =>//.
    by apply IHst.
  Qed.

  Lemma F_ext (sigma:@qvaluation M qVar) :
    forall (x:Molecule qVar)
      (f g: forall y:Molecule qVar, relation y x -> M.(positives) -> Prop),
      (forall (y:Molecule qVar) (p:relation y x) d,
         f y p d <-> g y p d) 
      -> forall d, SemPos_aux sigma x f d -> SemPos_aux sigma x g d.
  Proof.
    move => A f g H d.
    unfold SemPos_aux.
    elim.
    intros.
    apply (pv A _ p Delta v) => //.
    move : v H1 ; clear H0 d.
    apply F_ext_aux =>//. 
  Qed.

  Lemma Fix_F_inv sigma :
    forall (x:Molecule qVar) d (r s:Acc relation x),
      Fix_F (fun _ => M.(positives) -> Prop) (SemPos_aux sigma) r d 
      <-> Fix_F (fun _ => M.(positives) -> Prop) (SemPos_aux sigma) s d.
  Proof.
    move => A; induction (welf A).
    move => d r s.
    rewrite <- (Fix_F_eq _ _ r). 
    rewrite <- (Fix_F_eq _ _ s).
    split.
    apply (F_ext sigma _
                 (fun (y : Molecule qVar) (p : relation y x)  =>
                    Fix_F _ (SemPos_aux sigma) (Acc_inv r p))) => //=.
                                                             auto.
    apply (F_ext sigma _
                 (fun (y : Molecule qVar) (p : relation y x)  =>
                    Fix_F _ (SemPos_aux sigma) (Acc_inv s p))) => //=.
                                                             auto.
  Qed.

  (* Characterisation of SemPos: The first step is to have a
reformulation that looks much more like the definition of SemPos_aux,
but with the actual SemPos taking the place of the parameter f *)

  Lemma SemPos_Fix sigma :
    forall A tp, 
      SemPos sigma A tp 
      <-> PV A 
           (SemCont_aux sigma
                        (fun B tm
                         => exists h:relation B A, ortho (SemPos sigma B) tm)
           )
           tp.
  Proof.
    move => A tp; unfold SemPos; unfold Fix in |- *.
    rewrite <- Fix_F_eq.
    split; apply F_ext; intros; apply Fix_F_inv.
  Qed.

  (* Characterisation of SemPos: The second step is to have a
reformulation which drops the requirement B smaller than A in its use
of SemCont_aux (that requirement was needed for the well-foundedness
of the definition of SemPos) *)

  Lemma SemPosCont_aux1 sigma: 
    forall A st l (Delta:TypeTree qVar st l) tl (v:SemTree st), 
      (forall B : Molecule qVar, belong st Delta B -> relation B A)
      -> SemCont_aux sigma
                    (fun (B : Molecule qVar) (tm : negatives M) =>
                       ortho (SemPos sigma B) tm) 
                    st l Delta tl v      
      -> SemCont_aux sigma
                    (fun (B : Molecule qVar) (tm : negatives M) =>
                       exists _ : relation B A, ortho (SemPos sigma B) tm)
                    st l Delta tl v.
  Proof.
    move => A.
    induction st;
      dependent induction Delta ; move => tl v; 
      dependent induction v => H //; simpl.

      + (* move => [Sigma CV tll tm] H1; apply is_from_terms =>//. *) 
        move => H1.
        assert (belong sleafN (TleafN q) (substTerms tl q)).
        apply rel_leaf.
        assert (relation (substTerms tl q) A).
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
        move => [H0 [t [H1 H2]]].
        split =>//.
        exists t; split  => //.
        apply: IHst => //.
        move => B H5.
        apply: H.
        apply: rel_nodeq => //.
    Qed.

  Lemma SemPosCont_aux2 sigma: 
    forall A st l (Delta:TypeTree qVar st l) tl (v:SemTree st), 
      SemCont_aux sigma
                    (fun (B : Molecule qVar) (tm : negatives M) =>
                       exists _ : relation B A, ortho (SemPos sigma B) tm)
                    st l Delta tl v
      -> SemCont_aux sigma
                    (fun (B : Molecule qVar) (tm : negatives M) =>
                       ortho (SemPos sigma B) tm) 
                    st l Delta tl v.
  Proof.
    move => A.
    induction st;
      dependent induction Delta ; move => tl v; 
      dependent induction v => //; simpl.
    + by move => [_ H] //=.
    + by elim => H3 H4; split; [ apply IHst1 | apply IHst2].
    + by move => [H0 [t [H4 H]]]; split => //; exists t; split => //; apply: IHst.
    Qed.

  Lemma SemPosCont_aux sigma: 
    forall A tp, 
      PV A 
         (SemCont_aux sigma (fun B tm => ortho (SemPos sigma B) tm))
         tp      
      <-> PV A 
           (SemCont_aux sigma (fun B tm => exists h:relation B A, ortho (SemPos sigma B) tm))
           tp.
  Proof.
    intros.
    split => H;elim H;clear H;intros; apply (pv A _ p Delta v) => //=.
    + assert (forall B, belong (PatTree p) Delta B -> relation B A).
        * intros.
          apply (relation_base p Delta) => //=.
      apply SemPosCont_aux1 =>//.
      apply (SemPosCont_aux2 _ A) =>//.
  Qed.

  (* Characterisation of SemPos: the final step is to write the
definition we would actually like, and notice that, when unfolded, it
is equivalent to the actual definition by using the previous two
lemmas *)

  Theorem SemPosCont sigma : forall A tp, SemPos sigma A tp <-> PV A (@SemCont sigma) tp.
  Proof.
    intros;split; intro.
    apply SemPosCont_aux;apply SemPos_Fix => //=.
    apply SemPos_Fix;apply SemPosCont_aux => //=.
  Qed.

End TypeSemantics.

Arguments SemPos {M qVar} _ _ _.
Arguments SemCont {M qVar} _ {st} l _ _ _.
Arguments SemNeg {M qVar} _ _ _.
Arguments atomI {m qVar} _ _ _.
(* Arguments ToFamily {M qVar U V} _ _ _ _ _ _ . *)


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
          -> M0.(orth) (@SemC M0 (Context.(wextends) (PatTree p) w) 
                             (Context.(extends) v rho) c)
          -> M0.(orth) (M0.(I) rho f, M0.(tild) p v)
    }.

  Variable M:FullModel.

  (* We define the interpretation of a typing context as a predicate on
semantic contexts *)

  Definition compat {w w'} val: @ContType Sorts 
                                  (Atom w'.(QVar))
                                  (Molecule w'.(QVar))
                                  w
                             -> SContext M w -> Prop
    := fun Gamma rho => Contlift (w := w) M.(sortsI) (atomI val) (SemNeg val) Gamma rho.

  Lemma SemPosren {qVar qVar' l} (sigma:qvaluation qVar) (tau:qvaluation qVar') (ren:qVar -> qVar') 
               (tl:UTTermList l) (tl':UTTermList l) q a
      :  (forall xq, tau (ren xq) = sigma xq)
         -> SemTermList sigma tl = SemTermList tau tl'
         -> (SemPos (M := M) sigma (substTerms tl q) a <->
            SemPos (M := M) tau (substTerms tl' (Molecule_d.(qrename) ren q)) a).
  Proof.
    induction (welf (substTerms tl q)).
    move => H1 H2.
    rewrite SemPosCont.
    rewrite SemPosCont.
    split.
    elim.
    intros.
    Check pv.
    apply (pv M qVar' _ (@SemCont M _ tau) p Delta).
    admit.
  Qed.
  
  Lemma SemNegren {qVar qVar' l} (sigma:qvaluation qVar) (tau:qvaluation qVar') (ren:qVar -> qVar') 
               (tl:UTTermList l) (tl':UTTermList l) q a
      :  (forall xq, tau (ren xq) = sigma xq)
         -> SemTermList sigma tl = SemTermList tau tl'
         -> (SemNeg (M := M) sigma (substTerms tl q) a <->
            SemNeg (M := M) tau (substTerms tl' (Molecule_d.(qrename) ren q)) a).
  Proof.
    move => H1 H2.
    rewrite/SemNeg/ortho.
    split; intros;
    apply H.
    by rewrite (SemPosren _ _ _ _ tl') => //.
    by rewrite <- (SemPosren sigma _ _ tl tl') => //.
  Qed.

  Lemma SemPos2Treelift  qVar qVar' (sigma:qvaluation qVar) (tau:qvaluation qVar') (ren:qVar -> qVar') st qnew l Delta (tl:@UTTermList (Term qVar) l) tl' v 
  :  (forall xq, tau (ren xq) = sigma xq)
     -> correctNaming tau v qnew
     -> SemTermList sigma tl = SemTermList tau tl'
     -> SemCont (M := M)(st := st) sigma l Delta tl v
     -> Treelift M.(sortsI) (atomI tau) (SemNeg tau) (namedTypeTree ren l tl' Delta qnew) v.
  Proof.
    move : l Delta tl tl'.
    induction st => l Delta tl tl' H0 H1  H2; dependent induction v =>//=; dependent induction Delta =>//=; dependent induction qnew =>//=.
    rewrite (M.(atomIren) sigma tau ren tl tl') =>//.
    rewrite (SemNegren sigma tau ren tl tl') =>//.
    simpl in H1. 
    elim: H1 => H3 H4.
    move => [I1 I2]; split ; [apply (IHst1 _ _ _ _ tl) | apply (IHst2 _ _ _ _ tl) ] =>//.
    simpl in H1. 
    elim: H1 => H3 H4.
    move => [I1 [t [I2 I3]]]; split =>//.  
    apply (IHst _ _ _ _ (TermCons t Logic.I tl)) =>//.
    simpl.
    clear IHqnew IHDelta IHv.
    by rewrite I2 SemTermsVar H3 H2.
Qed.

  Lemma compatrename w w' Gamma rho sigma tau (renaming:w.(QVar) -> w'.(QVar))
  (pi: forall xq, tau (renaming xq) = sigma xq)
  : compat sigma Gamma rho -> compat tau (Contmap (w:=w)
                                 (fun i => i)
                                 (Atom_d.(qrename) renaming)
                                 (Molecule_d.(qrename) renaming)
                                 Gamma) rho.
  Proof.
    rewrite/compat/Contlift/Contmap;elim => H1 [H2 H3] /=.
                                              split => //;split.
    move => xp.
    move: (M.(atomIren) sigma tau renaming TermNil TermNil (Gamma.(readp) xp) (rho.(readp) xp)).
    simpl => H4.
    rewrite <- H4 => //.
    move => xn.
    move: (SemNegren sigma tau renaming TermNil TermNil (Gamma.(readn) xn) (rho.(readn) xn)).
    simpl => H4.
    rewrite <- H4 => //.
  Qed.

  Lemma substIgnoresTypes {A qVar Sigma l} (tl:TTermList Sigma l) X: 
    substTerms (TermListMap tl) X = substTerms (A := A)(qVar := qVar) tl X.
  Proof.
    induction l; dependent induction tl =>//=.
  Qed.

  (* Here is finally the Adequacy Lemma *)

  Hypothesis HValues: forall qVar sigma st (v:SemTree st) Delta,
                        SemCont (qVar:=qVar) sigma nil Delta TermNil v -> treevalue M v.

  Theorem adequacy:
    forall (w:World) (Gamma:TContext w),
      (forall pt A,
         TypingPos Gamma pt A
         ->  forall rho, compat rho.(readq) Gamma rho
                 -> SemPos rho.(readq) A (SemP M rho pt)
      )
      /\ (forall l st (v:TermTree st) Delta tl,
           TypingSub Gamma v Delta tl
           ->  forall rho, compat rho.(readq) Gamma rho
                   -> SemCont rho.(readq) l Delta (TermListMap tl) (SemSub M rho v)
        )
      /\ (forall nt A,
           TypingNeg Gamma nt A
           ->  forall rho, compat rho.(readq) Gamma rho
                   -> SemNeg rho.(readq) A (SemN M rho nt)
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
      apply SemPosCont; apply (pv _ _ _ _ _ Delta) =>//; apply (H rho H0)

      (* Typing a positive leaf of Sub *)
      | unfold SemCont => //= ;
        by rewrite substIgnoresTypes e; elim: H => _ [H _]; apply:H
      (* Typing a negative leaf of Sub *)
      | unfold SemCont => //= ;
        by rewrite substIgnoresTypes; apply H
      (* Typing a dummy leaf of Sub *)
      | unfold SemCont => //= 

      (* Typing a node of Sub *)
      | by unfold SemCont => //=; unfold SemCont in H, H0; split; [apply H|apply H0]

      (* Typing a qnode of Sub *)
      | unfold SemCont => //=; split;
        by [ apply (sortscompat M (Gamma.(readq))); move:H0;rewrite/compat/Contlift;elim => H2 _ 
        | exists r; split; [ | apply H]]
    (* by split; [apply (sortscompat M (readq Gamma) (readq rho) (proj1 H0)) | apply H] *)
      (* Typing a negative *)
      | simpl

      (* Typing an optional command *)
      | by exists (SemC M rho c); split; [| apply: H]

      (* Typing a cut *)
      | unfold SemCont => //=;unfold SemNeg, ortho in H;auto

      (* Typing a select *)
      | unfold SemC;unfold compat, SemNeg, ortho in H0;apply H0; auto
    ].
    
    (* Typing a negative *)
    unfold SemNeg, ortho => //=.
    intros.
    assert (PV M w.(QVar) A (@SemCont M w.(QVar) rho.(readq)) tp) by apply SemPosCont =>//=.
    elim H2;intros; clear H2.
    have H6: (exists csem : negatives M * positives M,
                SemOptionC (w:=Context.(wextends) (PatTree p) w)
                           M
                           (Context.(extends) v rho)
                           (f p) = Some csem
                /\ orth M csem).
    apply: (H p Delta) => //.
    apply (Context.(corr) (w:=w) (st:=PatTree p)).
    apply (SemPos2Treelift _ _ rho.(readq) _ _ _ _ _ _ TermNil)=> // .
    move => xq.
    apply (Context.(extends_qinject) (w:=w) (st:=PatTree p)).
    apply (Context.(extends_qnew) (w:=w) (st:=PatTree p)).
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
    apply (HValues _ rho.(readq) _ _ Delta) =>//.
    rewrite H9.
    done.
    move:H7.
    rewrite H9 => /= H7; injection H7; clear H7 => H7; rewrite H7 =>//.
  Qed.

End Adequacy.





(********************************************)

Section NonEmptyOrth.

  Record ValuesSystem :=
    {
      MW :> FullModelRaw ;
      Pvalue :MW.(primitives) -> Prop;
      Nvalue :MW.(negatives) -> Prop;
      orthVal : forall tn tp, MW.(orth) (tn,tp) -> Nvalue tn ;
      goodtval: qvaluation MW -> Prop;
      goodIgood: forall sigma, goodtval sigma -> forall fvar pri, sigma fvar pri -> Pvalue pri;
      nonempty : forall sigma, goodtval sigma -> forall A, exists pt, SemPos MW sigma A pt
    }.

  Fixpoint valuesTree (VS:ValuesSystem) {st} (v: @SemTree VS st): Prop
    := match v with
        | leafP X => VS.(Pvalue) X
        | leafN X => VS.(Nvalue) X
        | node st1 st2 v1 v2 => valuesTree VS v1 /\ valuesTree VS v2
      end.

  Record FullValuesSystem := 
    {
      VS :> ValuesSystem;

      stabVS {w} :
        forall (f: Reifiable) (rho: SContext VS w) (p: Patterns) (v: SemTree (PatTree p))  c,
          valuesTree VS v
          -> f p =cis= c
          -> VS.(orth) (SemC VS (Context.(extends) v rho) c)
          -> VS.(orth) (VS.(I) f rho, VS.(tild) p v)
    }.

  Definition toFM (M:FullValuesSystem) :=
    {| M0 := M.(VS);
       treevalue := fun w => @valuesTree M.(VS) w;
       stab := M.(@stabVS)
    |}.

  Variable M: FullValuesSystem.

  Definition valuesTVal (sigma: qvaluation M)
    := forall fvar pri, sigma fvar pri -> M.(Pvalue) pri.

  Lemma IsValue (sigma:qvaluation M):
    M.(goodtval) sigma
    -> forall st (v:@SemTree M st) Delta,
        SemCont M sigma Delta v 
        -> treevalue (toFM M) v.
  Proof.
    move => H0.
    elim.
    move => v; dependent inversion v; dependent induction Delta => /=; apply: M.(goodIgood) ; apply H0.
    move => v; dependent inversion v; dependent induction Delta => /= H1.
    have H2: (exists pt, SemPos M sigma b pt);
      [ apply: nonempty => //
      | elim: H2 => pt H2; 
                   apply: (M.(orthVal) _ pt); 
                   rewrite/SemNeg/ortho in H1; 
                   apply: H1 => //
      ].
    move => s1 H1 s2 H2 v Delta.
    dependent induction v; dependent induction Delta ; elim => H3 H4.
    split; [apply: (H1 _ Delta1)| apply: (H2 _ Delta2)] => //.
  Qed.

  Definition NEadequacy sigma H := adequacy (toFM M) sigma (IsValue sigma H). 

End NonEmptyOrth.

Print Assumptions adequacy.