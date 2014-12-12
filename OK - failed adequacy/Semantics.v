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

  Definition SemTree {M} := @Tree M.(terms) (fun _ => M.(primitives)) (fun _ => M.(negatives)).

  (* This is a useful abbreviation for type valuations *)

  Definition tvaluation {M} qVar := qVar -> M.(terms).

  (* In order to build a model of proof-terms, we require an
interpretation of terms, 
an interpretation of patterns, 
and an interpretation of the reifeied functions *)

  Record Model4PTerms := 
    {
      model :> Model4PTermsRaw;

      SemTerms {QVar}: @tvaluation model QVar -> Term QVar -> model.(terms);

      tild : forall p:Patterns, @SemTree model (PatTree p) nil -> model.(positives);

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
  Fixpoint SemSub {w} (rho:SContext w) {st} (v : TermTree st) l {struct v} :=
    match v in @TermTree _ s return SemTree s l with
      | tleafP xp => leafP (rho.(readp) xp)
      | tleafN tm => leafN (SemN rho tm)
      | tdummy    => dummy
      | tnode s1 s2 v1 v2 => node (SemSub rho (st:=s1) v1 l) (SemSub rho (st:=s2) v2 l)
      | tqnode s r v => let semr := (M.(SemTerms) rho.(readq) r) in
                       qnode semr (SemSub rho (st:=s) v (semr::l))
    end
  .

  (* The semantics of a positive term is a positive element of the model *)
  Definition SemP {w} (rho:SContext w) (pt : Pos) := 
    match pt with
        pos p v => M.(tild) p (SemSub rho v nil)
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
  | rel_leaf  : forall B Sigma tl, belong sleafN (leafN B) (substTerms (Sigma := Sigma) tl B)
  | rel_node1 : forall B s1 s2 t1 t2,
                  belong s1 t1 B -> belong (snode s1 s2) (node t1 t2) B
  | rel_node2 : forall B s1 s2 t1 t2,  
                  belong s2 t2 B -> belong (snode s1 s2) (node t1 t2) B
  | rel_nodeq : forall so B s t, 
                  belong (l := so::l) s t B
                  -> belong (sqnode s) (qnode so t) B
.

Inductive relation {qVar}
: Molecule qVar -> Molecule qVar -> Prop :=
  relation_base:
    forall p Delta A B, PatternsTyped p Delta A
               -> @belong qVar nil (PatTree p) Delta B
               -> relation B A.

Definition ParMol qVar := {l: list Sorts & TermFamily Molecule qVar l}.

Hypothesis welf: forall {QVar}, well_founded (@relation QVar).


(****************************************************************)
(* We now define the semantics of types according to a ModelRaw *)

Section TypeSemantics.

  Fixpoint SemSortedlistR M f (l:list Sorts)(tl:list M.(terms)): Prop
    := match l,tl with
        | nil, nil => True
        | cons so l', cons semr tl' => f so semr /\ SemSortedlistR M f l' tl'
        | _,_ => False
      end. 

  Record ModelRaw :=
    { model4PTerms :> Model4PTerms;
      sortsI: Sorts -> model4PTerms.(terms) -> Prop;
      sortscompat {qVar}: forall Sigma sigma,
                            (forall qvar:qVar, sortsI (Sigma qvar) (sigma qvar))
                            -> forall s t, 
                            SortingRel Sigma t s
                            -> sortsI s (model4PTerms.(SemTerms) sigma t);
      atomI {qVar} : @tvaluation model4PTerms qVar
                     -> Atom qVar
                     -> model4PTerms.(primitives) -> Prop;

      renamestable : forall qvar qvar' (a:Atom qvar) rho (ren: qvar -> qvar') p,
                       atomI (fun alpha => rho (ren alpha)) a p <-> atomI rho (Atom.(qrename) ren a) p
    }.
 
  Variable M: ModelRaw.

  Definition SemSortedlist := SemSortedlistR M M.(sortsI).

  Variable qVar:Type.
  Definition compattval Sigma sigma := forall qvar:qVar, M.(sortsI) (Sigma qvar) (sigma qvar).


  (* Here is the semantics of a list of well-sorted terms:
It is a list of semantical terms *)

  Fixpoint SemTermList sigma {Sigma l} (tl:@TermList qVar Sigma l)
    := match tl with
        | TermNil => nil
        | TermCons r so H l' tl' => (M.(SemTerms) sigma r)::(SemTermList sigma tl')
      end.

  (* The semantics of lists of terms satisfies the interpretation of lists of sorts *)

  (* Lemma WSSemTermList Sigma sigma (CV: compattval Sigma sigma) {l} (tl:@TermList qVar Sigma l)  *)
  (* : SemSortedlist l (SemTermList sigma tl). *)
  (* Proof. *)
  (*   induction tl => //=. *)
  (*   rewrite /SemSortedlist. *)
  (*   split. *)
  (*   apply (sortscompat M Sigma) => //. *)
  (*   apply IHtl => //. *)
  (* Defined. *)

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
                                -> forall tl, SemTree st tl -> Prop)
  : M.(positives) -> Prop :=
    pv : forall p Delta v,
           PatternsTyped p Delta A
           -> SemContext (PatTree p) nil Delta nil v 
           -> PV A SemContext (M.(tild) p v).

  Inductive ToFamily {U V} sigma f l (A: TermFamily U qVar l)
  : forall tl:list M.(terms), (* SemSortedlist l tl -> *) V -> Prop
    := is_from_terms Sigma (CV:compattval Sigma sigma) (tl:TermList Sigma l) tm :
        f (substTerms tl A) tm
        -> ToFamily sigma f l A (SemTermList sigma tl) (* (WSSemTermList Sigma sigma CV tl) *) tm.

  (* The interpretation (predicate on SemTrees) of a TypeTree Delta, given
a valuation sigma and a function f that provides the negative
interpretation of any molecule B in Delta *)

  Definition SemCont_aux (sigma:@tvaluation M qVar)
             (f : forall (A:Molecule qVar), M.(negatives) -> Prop)
             st
             l
             (Delta : TypeTree qVar st l)
             tl
             (v: @SemTree M st tl)
  : Prop
    := Treelift M.(sortsI) (ToFamily sigma (M.(atomI) sigma)) (ToFamily sigma f) l Delta tl v.

  (*   move : l Delta. *)
  (*   induction st => l Delta tl H v; inversion Delta; inversion v. *)
  (*   exact (ToFamily sigma (M.(atomI) qVar sigma) l X tl H X0). *)
  (*   exact (ToFamily sigma f l X tl H X0). *)
  (*   exact True. *)
  (*   exact (IHst1 l X tl H X1 /\ IHst2 l X0 tl H X2). *)
  (*   exact (exists H4 : M.(sortsI) so so0,  *)
  (*            IHst (so::l) X (so0::tl) (conj H4 H) X0). *)
  (* Defined. *)

  (* Definition SemCont_aux (sigma:@tvaluation M qVar) *)
  (*            (f : forall (A:Molecule qVar), M.(negatives) -> Prop) *)
  (*            st *)
  (*            l *)
  (*            (Delta : TypeTree qVar st l) *)
  (* : forall tl, SemSortedlist l tl -> @SemTree M st tl -> Prop. *)
  (*   move : l Delta. *)
  (*   induction st => l Delta tl H v; inversion Delta; inversion v. *)
  (*   exact (ToFamily sigma (M.(atomI) qVar sigma) l X tl H X0). *)
  (*   exact (ToFamily sigma f l X tl H X0). *)
  (*   exact True. *)
  (*   exact (IHst1 l X tl H X1 /\ IHst2 l X0 tl H X2). *)
  (*   exact (exists H4 : M.(sortsI) so so0,  *)
  (*            IHst (so::l) X (so0::tl) (conj H4 H) X0). *)
  (* Defined. *)

  (* Definition SemTTree {M} *)
  (*   := @Tree M.(terms) (fun _ => M.(primitives)) (fun _ => M.(negatives)). *)


  (* Check (fun sigma st  *)
  (*        => Treelift M.(sortsI) (myRelP sigma) (myRelN sigma)).  *)

(* Check SemCont. *)

  (* Lemma SemContAsTreeLift sigma:  *)
  (*   forall l st tl HWS *)
  (*     (Delta : TypeTree qVar st l) *)
  (*     (v: @SemTree M st tl), *)
  (*     SemCont sigma l Delta tl HWS v *)
  (*     <-> *)
  (*     Treelift M.(sortsI) (myRelP sigma) (myRelN sigma) l tl Delta v. *)
      

  (*                     M.(sortsI) *)
  (*                         () *)
  (*                             (fun _ _ => SemNeg rho.(readq)) ) *)



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


  (* Definition myRelP sigma := *)
  (*   fun l (_:list M.(terms)) (pa: (TermFamily Atom qVar l) *)
  (*                              £ { tl: list (M.(terms)) & SemSortedlist l tl} ) *)
  (*   => let (x, aux) := pa in *)
  (*     let (tl,HWS) := aux in *)
  (*     ToFamily sigma (M.(atomI) qVar sigma) l x tl HWS *)
  (* . *)

  (* Definition myRelN sigma := *)
  (*   fun l (_:list M.(terms)) (pa: (TermFamily Molecule qVar l) *)
  (*                              £ { tl: list (M.(terms)) & SemSortedlist l tl} ) *)
  (*   => let (x, aux) := pa in *)
  (*     let (tl,HWS) := aux in *)
  (*     ToFamily sigma (SemNeg sigma) l x tl HWS *)
  (* . *)



  (* The definition of SemPos is so far quite cryptic, because of the
induction that was necessary for the definition to be sound. The
theorem below characterise SemPos in a much more intuitive way, but
before that we need the following two lemmas. *)

  Lemma F_ext_aux (sigma:@tvaluation M qVar):
    forall (x:Molecule qVar)
      (f g: forall y:Molecule qVar, relation y x -> M.(positives) -> Prop),
      (forall (y:Molecule qVar) (p:relation y x) d,
         f y p d <-> g y p d) 
      -> forall st l (Delta:TypeTree qVar st l),
          forall tl' (v : SemTree st tl'),
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
    elim => Sigma H0 tl n.
    elim => h H1.
    apply is_from_terms => //. 
    exists h.
    move => tp H2.
    apply: H1.
    by apply H.

    case => H1 H2.
    by split; [apply: IHst1 |apply: IHst2].

    clear  IHv.
    elim => i H1.
    split =>//.
    by apply IHst.
  Qed.

  Lemma F_ext (sigma:@tvaluation M qVar) :
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
    forall A st l (Delta:TypeTree qVar st l) tl (v:SemTree st tl), 
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

      + move => [Sigma CV tll tm] H1; apply is_from_terms =>//. 
        assert (belong sleafN (leafN b) (substTerms tll b)).
        apply rel_leaf.
        assert (relation (substTerms tll b) A).
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
        elim.
        intros.
        split => //.
        apply: IHst => //.
        move => B H5.
        apply: H.
        apply: rel_nodeq => //.
    Qed.

  Lemma SemPosCont_aux2 sigma: 
    forall A st l (Delta:TypeTree qVar st l) tl (v:SemTree st tl), 
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
    + by move => [Sigma CV tll tm] H1; apply is_from_terms; elim:H1.
    + by elim => H3 H4; split; [ apply IHst1 | apply IHst2].
    + by move => [H4 H]; split => //; apply: IHst.
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
Arguments ToFamily {M qVar U V} _ _ _ _ _ _ .

(**************************************)

Section Adequacy.
  
  (* Even though we don't need to formalise a notion of reduction for
proof-terms, the Adequacy Lemma requires from a model that its
orthogonality relation be closed "under anti-reduction" *)

  Record FullModel := 
    {
      M0 :> ModelRaw;

      treevalue {st tl}: @SemTree M0 st tl -> Prop;

      stab {w} :
        forall (f: Reifiable) (rho: SContext M0 w) (p: Patterns) (v: SemTree (PatTree p) nil) c,
          treevalue v
          -> f p =cis= c
          -> M0.(orth) (@SemC M0 (Context.(wextends) (PatTree p) w) 
                             (Context.(extends) v rho) c)
          -> M0.(orth) (M0.(I) rho f, M0.(tild) p v)
    }.

  Variable M:FullModel.

  (* We define the interpretation of a typing context as a predicate on
semantic contexts *)

  Definition compat {w}: TContext w -> SContext M w -> Prop
    := fun Gamma rho => Contlift (w := w) M.(sortsI) (atomI rho.(readq)) (SemNeg rho.(readq)) Gamma rho.


  Lemma ToFamilyNil w (Gamma:TContext w) (rho: SContext M w) :
    let RelP := atomI in
    let RelN := SemNeg in
    let sigma := rho.(readq) in
    Contlift (sortsI M) (RelP sigma) (RelN sigma) Gamma rho
    <-> Contlift (sortsI M)
               (fun a b => ToFamily (M := M) (qVar:=w.(QVar)) sigma (RelP sigma) nil a nil b)
               (fun a b => ToFamily (M := M) (qVar:=w.(QVar)) sigma (RelN sigma) nil a nil b) 
               Gamma rho.
  Proof.
    split.
    move => H0.
    elim: H0 => H7 [H8 H9].
    split; [apply H7 | split].
    move => xp;
    exact (is_from_terms M w.(QVar) rho.(readq) (atomI (readq rho)) nil (readp Gamma xp) 
                                              Gamma.(readq) H7 TermNil (readp rho xp) (H8 xp)).
    move => xn;
    exact (is_from_terms M w.(QVar) rho.(readq) (SemNeg (readq rho)) nil (readn Gamma xn) 
                                              Gamma.(readq) H7 TermNil (readn rho xn) (H9 xn)).
    move => H0.
    elim: H0 => H7 [H8 H9].
    split; [apply H7 | split].
    by move => xp; elim (H8 xp); dependent induction tl.
    by move => xn; elim (H9 xn); dependent induction tl.
  Qed.


  (* Here is finally the Adequacy Lemma *)

  Theorem adequacy:
    forall (w:World) (Gamma:TContext w),
      (forall pt A,
         TypingPos Gamma pt A
         ->  forall rho, compat Gamma rho
                 -> (forall st (v:SemTree st nil) Delta,
                      SemCont rho.(readq) nil Delta nil v -> treevalue M v)
                 -> SemPos rho.(readq) A (SemP M rho pt)
      )
      /\ (forall l st (v:TermTree st) Delta tl,
           TypingSub Gamma v Delta tl
         ->  forall rho, compat Gamma rho
              -> (forall st (v:SemTree st nil) Delta,
                 SemCont rho.(readq) nil Delta nil v -> treevalue M v)
              -> let tls := SemTermList M w.(QVar) rho.(readq) tl in
                SemCont rho.(readq) l Delta 
                                   tls
                                   (SemSub M rho v tls)
        )
      /\ (forall nt A,
           TypingNeg Gamma nt A
           ->  forall rho, compat Gamma rho
                   -> (forall st (v:SemTree st nil) Delta,
                        SemCont rho.(readq) nil Delta nil v -> treevalue M v)
                   -> SemNeg rho.(readq) A (SemN M rho nt)
        )
      /\ (forall c,
           TypingOptionCommand Gamma c
           ->  forall rho, compat Gamma rho
                   -> (forall st (v:SemTree st nil) Delta,
                        SemCont rho.(readq) nil Delta nil v -> treevalue M v)
                   -> exists csem, (SemOptionC M rho c) = Some csem /\ M.(orth) csem)
      /\ (forall c,
           TypingCommand Gamma c
           ->  forall rho, compat Gamma rho
                   -> (forall st (v:SemTree st nil) Delta,
                        SemCont rho.(readq) nil Delta nil v -> treevalue M v)
                   -> M.(orth) (SemC M rho c))
  .
    apply typing_ind;intros;
    [
      (* Typing a positive *)
      apply SemPosCont; apply (pv _ _ _ _ _ Delta) =>//; apply (H rho H0 H1)

      (* Typing a positive leaf of Sub *)
      | unfold SemCont => //= ;
        apply is_from_terms;
        [rewrite/compattval; apply H| rewrite /TermFamily/fset/map e; apply H]

      (* Typing a negative leaf of Sub *)
      | unfold SemCont => //=;
        by apply is_from_terms; [rewrite/compattval; apply H0 | apply H]

      (* Typing a dummy leaf of Sub *)
      | unfold SemCont => //= 

      (* Typing a node of Sub *)
      | by unfold SemCont => //=; unfold SemCont in H, H0; split; [apply H|apply H0]

      (* Typing a qnode of Sub *)
      | unfold SemCont => //=;
        by split; [apply (sortscompat M (readq Gamma) (readq rho) (proj1 H0)) | apply H]
      (* Typing a negative *)
      | simpl

      (* Typing an optional command *)
      | exists (SemC M rho c); split; by [| apply: H]

      (* Typing a cut *)
      | unfold SemCont => //=;unfold SemNeg, ortho in H;auto

      (* Typing a select *)
      | unfold SemC;unfold compat, SemNeg, ortho in H0;apply H0; auto
    ].
    
    (* Typing a negative *)
    unfold SemNeg, ortho => //=.
    intros.
    assert (PV M w.(QVar) A (@SemCont M w.(QVar) rho.(readq)) tp) by apply SemPosCont=>//=.
    elim H3;intros.
    have H6: (exists csem : negatives M * positives M,
                SemOptionC (w:=Context.(wextends) (PatTree p) w)
                           M
                           (Context.(extends) v rho)
                           (f p) = Some csem
                /\ orth M csem).
    apply: (H p Delta) => //.
    rewrite/compat.
    rewrite/compat in H0.
    move: (proj1 (ToFamilyNil _ _ _) H0); clear H0 => H0.
    move :
      (Context.(corr) (w:=w) (st:=PatTree p)
                      M.(sortsI)
                          (ToFamily rho.(readq) (atomI rho.(readq)))
                          (ToFamily rho.(readq) (SemNeg rho.(readq)))
                          Gamma rho Delta v H5 H0
      ).
    clear H0 => H0.
    move: (proj2 (ToFamilyNil _ _ _) H0); clear H0 => H0.

    rewrite <- ToFamilyNil.



    => //.
        elim: H5 => csem ; elim => H6 H7.
    move : H6.
    remember (f p) as u.
    move: Hequ.
    elim: u => //.
                move => a H8 H9.
    apply (M.(stab) (w:=w) _ _ _ _ a).
    apply: (H36 _ _  Delta) =>//.
      by rewrite <- H8.
    inversion H9;  rewrite H6 =>//.
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
      goodtval: tvaluation MW -> Prop;
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

  Definition valuesTVal (sigma: tvaluation M)
    := forall fvar pri, sigma fvar pri -> M.(Pvalue) pri.

  Lemma IsValue (sigma:tvaluation M):
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