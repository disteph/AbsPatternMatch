Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.
Unset Printing Implicit Defensive.
Typeclasses eauto := 1.

Require Import mathcomp.ssreflect.ssreflect List Basic LAF LAFwE.

Section LAFwEL.

  Definition RenamingContexts `{QuantifyingStructureswE} w
    := ContextswE w.(PLab) w.(NLab) w.(QLab).

  Fixpoint ExtstL2Extst `{QSwE : QuantifyingStructureswE}
           w st st'
           (qnew: @Dec 
                    (QLab (wextendsE st' w))
                    (PLab (wextendsE st' w))
                    (NLab (wextendsE st' w)) st)
  : @Dec (QLab (wextendsE st' w)) unit unit st
    :=
      match qnew with
        | leafP _ => leafP tt
        | leafN _ => leafN tt
        | dummy => dummy
        | node _ _ qnew1 qnew2 => node (ExtstL2Extst qnew1) (ExtstL2Extst qnew2)
        | qnode _ t qnew' => qnode t (ExtstL2Extst qnew')
      end.

  Print QSTypeswE.

  Check @is_eq.
  Check renInst.
  Check @QSTwE2QST_base.
  Check QWorld.
  Set Printing All.
  Definition QSTypeswEL2QSTypeswE_base `(QSwE : QuantifyingStructureswE)
             AtomV 
             MoleculeV
             is_eqV
             (RC:forall w, RenamingContexts w)
             (ExtrenL : forall (w:World _) st, RC (wextendsE st w) w)
             (ExtstL : forall (w:World _) st, @Dec 
                                           (QLab (wextendsE st w))
                                           (PLab (wextendsE st w))
                                           (NLab (wextendsE st w)) st)
             is_eq_renV
  : QSTypeswE (AtomV := AtomV) MoleculeV is_eqV
    := 
      {|
        Extren w st := readE (ExtrenL w st);
        Extst w st := ExtstL2Extst (ExtstL w st);
        is_eq_ren := is_eq_renV
      |}.

  Class QSTypeswEL `{QuantifyingStructureswE} AtomV MoleculeV is_eqV is_eq_renV
    := 
      {
        RC      : forall w, RenamingContexts w;
        ExtrenL : forall (w:World _) st, RC (wextendsE st w) w;
        ExtstL  : forall (w:World _) st, @Dec 
                                      (QLab (wextendsE st w))
                                      (PLab (wextendsE st w))
                                      (NLab (wextendsE st w)) st;
        QSTwELasQSTwE := QSTypeswEL2QSTypeswE_base (AtomV := AtomV) 
                                                  (MoleculeV:= MoleculeV)
                                                  (is_eqV := is_eqV)
                                                  (RC := RC)
                                                  ExtrenL ExtstL
                                                  is_eq_renV;
        RCrenProp w : renProp (RC w);
        RCstProp w : stProp (RC w)
      }.

  Coercion QSTwELasQSTwE: QSTypeswEL >-> QSTypeswE.
  (* Canonical QSTypeswEL2QSTypeswE `(QSTypeswEL) := QSTypeswEL2QSTypeswE_base MoleculeV is_eqV. *)

  Class LAFswEL `{QSTwEL: QSTypeswEL} {PatternsV PatDecV PatternsTypedV}
    := {
        asLAFwE :
        LAFswE (QSTV:=QSTwEL) 
             (PatternsV := PatternsV) (PatDecV := PatDecV) (PatternsTypedV := PatternsTypedV);
        Renmap w0 w1 w2 : RC w0 w1 -> RC w1 w2 -> RC w0 w2;
        RenmapProp w0 w1 w2 (pi1:RC w0 w1) (pi2:RC w1 w2)
        : ContMap (H := asLAFwE) (readE pi1) (readp pi1) (readn pi1) pi2 (Renmap pi1 pi2);

        freeE {qLab : Type} : Terms qLab -> qLab -> Prop;

        mapdistrib (qLab qLab' : QWorld (asLAF (LAFswE := asLAFwE)))
                   (w: World (asLAF (LAFswE := asLAFwE)))
                   (f1: Inst Atom qLab -> Inst Atom qLab')
                   (f2: Inst Molecule qLab -> Inst Molecule qLab')
                   (Gamma: TCV qLab w)
                   st
                   (Delta: @Dec (Sorts (QSwE2QS asLAFwE))
                            (Inst Atom qLab')
                            (Inst Molecule qLab')
                            st)
                   (Delta': @Dec (Sorts (QSwE2QS asLAFwE))
                                 (Inst Atom qLab)
                                 (Inst Molecule qLab)
                                 st)
        : Declift (fun s1 s2 => s1 = s2)
                  (fun c c' => c = f1 c')
                  (fun c c' => c = f2 c')
                  Delta Delta'
          -> ContMap (H := asLAFwE) (fun i => i) (fun i => i) (fun i => i)
                    (TCmap f1 f2 (extends Delta' Gamma)) (extends Delta (TCmap f1 f2 Gamma))
      }.

  Coercion asLAFwE : LAFswEL >-> LAFswE.

  Context `(L:LAFswEL).

  Definition renaminglift {w wnew} st (rho: RC wnew w)
    := extends (ExtstL wnew st) (Renmap (ExtrenL wnew st) rho).

  Fixpoint liftP {w wnew : World asLAF} (rho:RC wnew w) (tp:Pos w) {struct tp} 
  : Pos wnew
    := match tp with
          pos p v  => pos p (liftTree rho v)
      end
  with liftTree {w wnew : World asLAF}{st} (rho:RC wnew w) (v: @TermDec asLAF w st) {struct v} 
       : TermDec wnew st
       := match v with
           | tleafP xp => tleafP (readp rho xp)
           | tleafN tn => tleafN (liftN rho tn)
           | tdummy => tdummy wnew
           | tnode _ _ v1 v2 => tnode (liftTree rho v1) (liftTree rho v2)
           | tqnode _ t v' => tqnode
                               (LAF := asLAF (LAFswE := L))
                               (lift2Terms (readE rho) t) (liftTree rho v')
         end
  with liftN {w wnew} (rho:RC wnew w) (tn:@Neg asLAF w) {struct tn}
       : Neg wnew
       := match tn with
             rei f => rei (fun p => liftOC (renaminglift (PatDec p) rho) (f p))
         end
  with liftOC {w wnew: World asLAF} (rho:RC wnew w) (oc:OptionCommand w) {struct oc}
       : OptionCommand wnew
       := match oc with
           | none => none wnew
           | some c => some(liftC rho c)
         end
  with liftC {w wnew: World asLAF} (rho:RC wnew w) (c:Command w)  {struct c}
       : Command wnew
       := match c with
           | cut tn tp => cut (liftN rho tn) (liftP rho tp)
           | select xn tp => select (readn rho xn) (liftP rho tp)
         end
  .

  Fixpoint freeP 
           {w : World (asLAF (LAFswE := L))}
           {A:World asLAF -> Type}
           (leafPf: forall w, w.(PLab) -> A w -> Prop)
           (leafNf: forall w, w.(NLab) -> A w -> Prop)
           (qnodef: forall w, Terms (q:= asLAF) w.(QLab) -> A w -> Prop)
           (read: forall wnew w, RC wnew w -> A w -> A wnew)
           (tp:Pos w) (xp: A w) {struct tp} 
  : Prop
    := match tp with
          pos p v  => freeDec leafPf leafNf qnodef read v xp
      end
  with freeDec {w : World asLAF}
               {A:World asLAF -> Type}
               (leafPf: forall w, w.(PLab) -> A w -> Prop)
               (leafNf: forall w, w.(NLab) -> A w -> Prop)
               (qnodef: forall w, Terms (q:= asLAF) w.(QLab) -> A w -> Prop)
               (read: forall wnew w, RC wnew w -> A w -> A wnew)
               {st} (v: @TermDec asLAF w st) (xp:A w) {struct v} 
       : Prop
       := match v with
           | tleafP xp' => leafPf w xp' xp
           | tleafN tn => freeN leafPf leafNf qnodef read tn xp
           | tdummy => False
           | tnode _ _ v1 v2 => (freeDec leafPf leafNf qnodef read v1 xp)
                               \/(freeDec leafPf leafNf qnodef read v2 xp)
           | tqnode _ t v' => (qnodef w t xp)
                             \/(freeDec leafPf leafNf qnodef read v' xp)
         end
  with freeN {w: World asLAF}
              {A:World asLAF -> Type}
              (leafPf: forall w, w.(PLab) -> A w -> Prop)
              (leafNf: forall w, w.(NLab) -> A w -> Prop)
              (qnodef: forall w, Terms (q:= asLAF) w.(QLab) -> A w -> Prop)
              (read: forall wnew w, RC wnew w -> A w -> A wnew)
              (tn:@Neg asLAF w) (xp:A w) {struct tn}
       : Prop
       := match tn with
             rei f => exists p, freeOC (w:=wextends (PatDec p) w) leafPf leafNf qnodef read 
                                 (f p) (read _ _ (ExtrenL w (PatDec p)) xp)
         end
  with freeOC {w: World asLAF}
               {A:World asLAF -> Type}
               (leafPf: forall w, w.(PLab) -> A w -> Prop)
               (leafNf: forall w, w.(NLab) -> A w -> Prop)
               (qnodef: forall w, Terms (q:= asLAF) w.(QLab) -> A w -> Prop)
               (read: forall wnew w, RC wnew w -> A w -> A wnew)
               (oc:OptionCommand w) (xp:A w) {struct oc}
       : Prop
       := match oc with
           | none => False
           | some c => freeC leafPf leafNf qnodef read c xp
         end
  with freeC {w: World asLAF}
              {A:World asLAF -> Type}
              (leafPf: forall w, w.(PLab) -> A w -> Prop)
              (leafNf: forall w, w.(NLab) -> A w -> Prop)
              (qnodef: forall w, Terms (q:= asLAF) w.(QLab) -> A w -> Prop)
              (read: forall wnew w, RC wnew w -> A w -> A wnew)
              (c:Command w) (xp:A w) {struct c}
       : Prop
       := match c with
           | cut tn tp => (freeN leafPf leafNf qnodef read tn xp)
                         \/(freeP leafPf leafNf qnodef read tp xp)
           | select xn tp => (leafNf w xn xp)
                            \/(freeP leafPf leafNf qnodef read tp xp)
         end
  .

  Definition freepP w := freeP (w:=w) (fun w xp' xp => xp=xp') (fun _ _ _ => False) (fun _ _ _ => False) (fun wnew w rho xp => readp rho xp).
  Definition freepN w := freeN (w:=w) (fun w xp' xp => xp=xp') (fun _ _ _ => False) (fun _ _ _ => False) (fun wnew w rho xp => readp rho xp).
  Definition freepDec w st := freeDec (w:=w) (st:=st) (fun w xp' xp => xp=xp') (fun _ _ _ => False) (fun _ _ _ => False) (fun wnew w rho xp => readp rho xp).
  Definition freepOC w := freeOC (w:=w) (fun w xp' xp => xp=xp') (fun _ _ _ => False) (fun _ _ _ => False) (fun wnew w rho xp => readp rho xp).
  Definition freepC w := freeC (w:=w) (fun w xp' xp => xp=xp') (fun _ _ _ => False) (fun _ _ _ => False) (fun wnew w rho xp => readp rho xp).

  Definition freenP w := freeP (w:=w) (fun _ _ _ => False) (fun w xn' xn => xn=xn') (fun _ _ _ => False) (fun wnew w rho xn => readn rho xn).
  Definition freenN w := freeN (w:=w) (fun _ _ _ => False) (fun w xn' xn => xn=xn') (fun _ _ _ => False) (fun wnew w rho xn => readn rho xn).
  Definition freenDec w st := freeDec (w:=w) (st:=st) (fun _ _ _ => False) (fun w xn' xn => xn=xn') (fun _ _ _ => False) (fun wnew w rho xn => readn rho xn).
  Definition freenOC w := freeOC (w:=w) (fun _ _ _ => False) (fun w xn' xn => xn=xn') (fun _ _ _ => False) (fun wnew w rho xn => readn rho xn).
  Definition freenC w := freeC (w:=w) (fun _ _ _ => False) (fun w xn' xn => xn=xn') (fun _ _ _ => False) (fun wnew w rho xn => readn rho xn).

  Definition freeEP w := freeP (w:=w) (fun _ _ _ => False) (fun _ _ _ => False) (fun w t xq => freeE t xq) (fun wnew w rho xq => readE rho xq).
  Definition freeEN w := freeN (w:=w) (fun _ _ _ => False) (fun _ _ _ => False) (fun w t xq => freeE t xq) (fun wnew w rho xq => readE rho xq).
  Definition freeEDec w st := freeDec (w:=w) (st:=st) (fun _ _ _ => False) (fun _ _ _ => False) (fun w t xq => freeE t xq) (fun wnew w rho xq => readE rho xq).
  Definition freeEOC w := freeOC (w:=w) (fun _ _ _ => False) (fun _ _ _ => False) (fun w t xq => freeE t xq) (fun wnew w rho xq => readE rho xq).
  Definition freeEC w := freeC (w:=w) (fun _ _ _ => False) (fun _ _ _ => False) (fun w t xq => freeE t xq) (fun wnew w rho xq => readE rho xq).

  Definition embeds {qLab w1 w2} 
             (Gamma1: TCV (LAFswE := L) qLab w1) 
             (Gamma2: TCV qLab w2) 
             (rho: RC w2 w1) :=
    (forall xq:w1.(QLab), Gamma2.(readE) (rho.(readE) xq) = Gamma1.(readE) xq)
    /\
    (forall xp:w1.(PLab), Gamma2.(readp) (rho.(readp) xp) = (Gamma1.(readp) xp))
    /\
    (forall xn:w1.(NLab), Gamma2.(readn) (rho.(readn) xn) = (Gamma1.(readn) xn))
  .

  Remark Rem1 (w wnew : World (asLAF (LAFswE:= L))) st (rho: RC wnew w)
  : forall xq: w.(QLab),
      (readE (renaminglift st rho) (readE (ExtrenL w st) xq))
      =
      (readE (ExtrenL wnew st)) (readE rho xq) 
  .
  Proof.
    move => xq.
    rewrite RCrenProp.
    refine ((fun H => _ )(RenmapProp (ExtrenL wnew st) rho)).
    elim: H0 => H0 _.
    rewrite H0 => //.
  Qed.

  Remark Rem2 
         (qLab1 qLab2: QWorld (asLAF (LAFswE:= L))) 
         (w1 w2 : World (asLAF (LAFswE:= L)))
         (Gamma1: TCV qLab1 w1)
         (Gamma2: TCV qLab2 w2)
         st
         (rho: RC w2 (wextendsE st w1))
         (Delta: @Dec (Sorts (QSwE2QS L))
                       (Inst Atom qLab2)
                       (Inst Molecule qLab2)
                       st)
         (Delta': @Dec (Sorts (QSwE2QS L))
                  (Inst Atom qLab1)
                  (Inst Molecule qLab1)
                  st)
         (f1: Inst Atom qLab1 -> Inst Atom qLab2)
         (f2: Inst Molecule qLab1 -> Inst Molecule qLab2)
  :
    Declift (fun s1 s2 => s1 = s2)
            (fun c c' => c = f1 c')
            (fun c c' => c = f2 c')
            Delta Delta'
    -> embeds (extends Delta (TCmap f1 f2 Gamma1)) Gamma2 rho
    -> embeds (TCmap f1 f2 (extends Delta' Gamma1)) Gamma2 rho.
  Proof.
    move => H0 [H1 [H2 H3]].
    move: (mapdistrib Gamma1 H0) => [H4 [H5 H6]].
    by split;
    [ move => xq; rewrite H1 H4
    | split ;
      [move => xp; rewrite H2 H5
      | move => xn; rewrite H3 H6]
    ].
  Qed.
  
  Hypothesis RenamingCorrelation
  : forall (qLab: QWorld (asLAF (LAFswE:= L))) 
      (w1 w2 : World (asLAF (LAFswE:= L)))
      (Gamma1: TCV qLab w1)
      (Gamma2: TCV qLab w2)
      (rho: RC w2 w1)
      st
      (Delta: @Dec (Sorts (QSwE2QS L))
               (Inst Atom qLab)
               (Inst Molecule qLab)
               st),
      embeds Gamma1 Gamma2 rho
      -> embeds (extends Delta Gamma1) (extends Delta Gamma2) (renaminglift st rho).

  Lemma Lem55:
    forall (w wnew: World (asLAF (LAFswE:= L)))
      (rho: RC wnew w)
      st st' ls delta delta'
      (Delta:TypingDec st ls),
      Declift (st := st) 
              (fun s s' => s = readE(renaminglift st' rho) s')
              (fun c c' => True)
              (fun c c' => True)
              delta
              delta'
      ->
      forall (tl: TList (wextends st' w).(QLab) ls),
      Declift (st := st) 
              (fun s s' => s = s')
              (fun c c' => c = renInst (readE(renaminglift st' rho)) c')
              (fun c c' => c = renInst (readE(renaminglift st' rho)) c')
              (InstTypingDec delta (renTList (readE(renaminglift st' rho)) tl) Delta)
              (InstTypingDec delta' tl Delta).
  Proof.
    move => w wnew rho st st' l delta delta' Delta.
    induction Delta => H0 tl //.

    move: H0.
    move: (Decstruct (snode s1 s2) delta) => [v1 [v2 Hdelta]].
    rewrite Hdelta.
    move: (Decstruct (snode s1 s2) delta') => [v1' [v2' Hdelta']].
    rewrite Hdelta'.
    simpl. 
    move => [H1 H2].
    by split; [apply (IHDelta1 v1 v1') | apply (IHDelta2 v2 v2')].

    move: H0.
    move: (Decstruct (sqnode s) delta) => [v0 [t Hdelta]].
    rewrite Hdelta.
    move: (Decstruct (sqnode s) delta') => [v0' [t' Hdelta']].
    rewrite Hdelta'.
    simpl.
    move => [H0 H1].
    split =>//.
    rewrite H0.
    move:(IHDelta v0 v0' H1 (TermCons so (asT t') tl)).
    simpl.
    by rewrite lift2Terms_asT.
  Qed.

  Lemma Lem55bis
        (w wnew: World (asLAF (LAFswE:= L)))
        (rho: RC wnew w)
        st st' ls delta delta'
        (Delta:TypingDec st ls)
  : Declift (st := st) 
            (fun s s' => s = readE(renaminglift st' rho) s')
            (fun c c' => True)
            (fun c c' => True)
            delta
            delta'
    ->
    forall (tl: TList w.(QLab) ls),
      Declift (st := st) 
              (fun s1 s2 => s1 = s2)
              (fun c c' => c = renInst (readE(renaminglift st' rho)) c')
              (fun c c' => c = renInst (readE(renaminglift st' rho)) c')
              (InstTypingDec delta
                             (renTList (readE (ExtrenL wnew st')) (renTList (readE rho) tl))
                             Delta)
              (InstTypingDec delta'
                             (renTList (readE (ExtrenL w st')) tl)
                             Delta).
  Proof.
    move => H0 tl.
    refine (_ (_ :renTList (readE (ExtrenL wnew st')) (renTList (readE rho) tl)
               = renTList (readE(renaminglift st' rho)) (renTList (readE (ExtrenL w st')) tl))).
    move => H1.
    rewrite H1.
    apply Lem55 => //.
    rewrite -(renTList_comp (f3 := comp (readE (ExtrenL wnew _)) (readE rho))).
    rewrite (renTList_comp (f3 := comp (readE (ExtrenL wnew _)) (readE rho))
                           (f2 := readE (renaminglift _ rho))
                           (f1 := readE (ExtrenL w _))
            ) => //.
    by move => xq; rewrite /comp -Rem1.  
    by move => xq; rewrite /comp.
  Qed.

  Remark Rem3 (w wnew: World (asLAF (LAFswE:= L))) st0 st delta delta'
      (rho: RC wnew w)
  :
    Declift (st := st) 
      (fun (s : QLab (wextendsE st0 wnew)) (xq : QLab (wextendsE st0 w)) =>
         s = readE (extends (ExtstL wnew st0) (Renmap (ExtrenL wnew st0) rho)) xq)
      (fun (_ : PLab (wextendsE st0 wnew)) (_ : unit) => True)
      (fun (_ : NLab (wextendsE st0 wnew)) (_ : unit) => True) 
      delta delta' ->
    Declift
      (fun (s : QLab (wextendsE st0 wnew)) (s' : QLab (wextendsE st0 w)) =>
         s = readE (extends (ExtstL wnew st0) (Renmap (ExtrenL wnew st0) rho)) s')
      (fun _ _ : unit => True) (fun _ _ : unit => True)
      (ExtstL2Extst delta) delta'.
  Proof.
    induction st.
    move: (Decstruct sleafP delta) => [a H0]; rewrite H0 => //.
    move: (Decstruct sleafN delta) => [a H0]; rewrite H0 => //.
    move: (Decstruct sdummy delta) => H0; rewrite H0 => //.
    move: (Decstruct (snode st1 st2) delta) => [delta1 [delta2 H0]]; rewrite H0 => //.
    move: (Decstruct (snode st1 st2) delta') => [delta1' [delta2' H0']]; rewrite H0'; simpl;
     move => [H1 H2].
    split;[apply IHst1 | apply IHst2] => //.
    move: (Decstruct (sqnode st) delta) => [delta0 [t H0]]; rewrite H0.
    move: (Decstruct (sqnode st) delta') => [delta0' [t' H0']]; rewrite H0'; simpl.
    move => [H1 H2]; split =>//.
    apply IHst => //.
  Qed.

  Lemma Lem55ter:
    forall (w wnew: World (asLAF (LAFswE:= L)))
      (rho: RC wnew w)
      st ls
      (Delta:TypingDec st ls) 
      (tl: TList w.(QLab) ls),
      Declift (st := st) 
              (fun s1 s2 => s1 = s2)
              (fun c c' => c = renInst (readE(renaminglift st rho)) c')
              (fun c c' => c = renInst (readE(renaminglift st rho)) c')
              (InstTypingDec (ExtstL2Extst (ExtstL wnew st))
                             (renTList (readE (ExtrenL wnew st)) (renTList (readE rho) tl))
                             Delta)
              (InstTypingDec (ExtstL2Extst (ExtstL w st))
                             (renTList (readE (ExtrenL w st)) tl)
                             Delta).
  Proof.
    intros.
    apply Lem55bis.
    rewrite /renaminglift.
    refine ((fun H =>_) (RCstProp)).
    refine (_ (H0 (wextendsE st wnew))).
    clear H0.
    rewrite /stProp => H0.
    refine (_ (H0 w st (Renmap (ExtrenL wnew st) rho) (ExtstL wnew st))).
    clear H0.
    rewrite /Extst.
    simpl.
    apply Rem3.
  Qed.

  Definition Tembeds {w1 w2 : World (asLAF (LAFswE:= L))} 
             (Gamma1: TCV w1.(QLab) w1) 
             (Gamma2: TCV w2.(QLab) w2) 
             (rho: RC w2 w1) :=
    embeds (TCmap (renInst (readE rho)) (renInst (readE rho)) Gamma1) Gamma2 rho.

  Lemma Lem56 :
    forall (w wnew : World (asLAF (LAFswE:= L)))
      (Gamma1: TCV w.(QLab) w) 
      (Gamma2: TCV wnew.(QLab) wnew) 
      (rho: RC wnew w)
      st ls 
      (Delta:TypingDec st ls) 
      (tl: TList w.(QLab) ls),
      Tembeds Gamma1 Gamma2 rho
      ->
      Tembeds
        (extends
           (InstTypingDec (ExtstL2Extst (ExtstL w st))
                          (renTList (readE (ExtrenL w st)) tl) Delta)
           (TCmap (renInst (readE (ExtrenL w st)))
                  (renInst (readE (ExtrenL w st))) Gamma1))
        (extends
           (InstTypingDec (ExtstL2Extst (ExtstL wnew st))
                          (renTList (readE (ExtrenL wnew st))
                                    (renTList (readE rho) tl)) Delta)
           (TCmap (renInst (readE (ExtrenL wnew st)))
                  (renInst (readE (ExtrenL wnew st))) Gamma2))
        (renaminglift st rho).
  Proof.
    move => w wnew Gamma1 Gamma2 rho st ls Delta tl.
    rewrite /Tembeds.
    rewrite{1}/embeds. 
    elim  => H0 [H1 H2].
    apply: (Rem2 (Delta := (InstTypingDec (ExtstL2Extst (ExtstL wnew st))
           (renTList (readE (ExtrenL wnew st)) (renTList (readE rho) tl))
           Delta))).
    apply: Lem55ter.
    apply: RenamingCorrelation.
    refine (_ (TCmapProp (renInst (readE (ExtrenL wnew st)))
                         (renInst (readE (ExtrenL wnew st))) Gamma2));
      move => [H3 [H4 H5]].
    refine (_ (TCmapProp  (renInst (readE (renaminglift st rho)))
                          (renInst (readE (renaminglift st rho)))
                          (TCmap (renInst (readE (ExtrenL w st)))
                                 (renInst (readE (ExtrenL w st))) Gamma1)));
      move => [H6 [H7 H8]].
    refine (_ (TCmapProp (renInst (readE (ExtrenL w st))) 
                         (renInst (readE (ExtrenL w st)))
                         Gamma1));
      move => [H9 [H10 H11]].
    refine (_ (TCmapProp (renInst (readE rho)) 
                         (renInst (readE rho))
                         Gamma1)); move => [H12 [H13 H14]].
    split.
    move => xq. 
    rewrite H3 H6 H9 H0 H12 => //.
    split;
      [
        move => xp;
        rewrite H4 H7 H10 H1 H13
      | move => xn;
        rewrite H5 H8 H11 H2 H14
      ];
    (rewrite -(renInst_comp (f3 := comp (readE (ExtrenL wnew st)) (readE rho)));
    [ apply (renInst_comp (f3 := comp (readE (ExtrenL wnew st)) (readE rho)));
    by move => xq; rewrite /comp -Rem1
    | by move => xq; rewrite /comp]).
  Qed.

  Theorem RenamingTyping:
    forall (w:World (asLAF (LAFswE := L))) (Gamma1: TContext w),
      (forall pt A,
         PosTyping Gamma1 pt A
         -> forall wnew (Gamma2: TContext wnew) (rho: RC wnew w),
             Tembeds Gamma1 Gamma2 rho
             -> PosTyping Gamma2 (liftP rho pt) (renInst (readE rho) A))
      /\ (forall l st (v:TermDec w st) Delta tl,
           DecTyping (l:=l) Gamma1 v Delta tl
           -> forall wnew (Gamma2: TContext wnew) (rho: RC wnew w),
               Tembeds Gamma1 Gamma2 rho
               -> DecTyping Gamma2 (liftTree rho v) Delta (renTList (readE rho) tl))
      /\ (forall nt A,
           NegTyping Gamma1 nt A 
           -> forall wnew (Gamma2: TContext wnew) (rho: RC wnew w),
               Tembeds Gamma1 Gamma2 rho
               -> NegTyping Gamma2 (liftN rho nt) (renInst (readE rho) A))
      /\ (forall c,
           OptionCommandTyping Gamma1 c
           -> forall wnew (Gamma2: TContext wnew) (rho: RC wnew w),
               Tembeds Gamma1 Gamma2 rho
               -> OptionCommandTyping Gamma2 (liftOC rho c))
      /\ (forall c,
           CommandTyping Gamma1 c
           -> forall wnew (Gamma2: TContext wnew) (rho: RC wnew w),
               Tembeds Gamma1 Gamma2 rho
               -> CommandTyping Gamma2 (liftC rho c)).
  Proof.
    apply typing_ind;intros;
    [
      apply: (typingpos p0) => //; apply: H0 => //
    | by elim: H0 => H1 [H3 _]; apply: typingsub_leafl;
                 rewrite /Treadp;
                 simpl;
                 rewrite (H3 xp);
                 move: (TCmapProp (renInst (readE rho))(renInst (readE rho)) Gamma) => [_ [H4 _]];
                 rewrite H4;
                 apply (is_eq_ren i)
    | by apply: typingsub_leafr; apply H0 => //;
      move => xq; move :(H1 xq);
      move: (TCmapProp (renInst (readE rho))(renInst (readE rho)) Gamma) => [H2 _];
      rewrite H2
    | by apply: typingsub_dummy
    | by apply: typingsub_node; [apply H0| apply H1] => //
    | by apply: typingsub_qnode; 
      [ apply: (renSorting _ s0); elim: H1 => H1 _ ;
          move => xq; move :(H1 xq);
          move: (TCmapProp (renInst (readE rho))(renInst (readE rho)) Gamma) => [H2 _];
          rewrite H2
      | apply H0 => // ]
    | apply typingneg
    | by apply: typingoption; apply: H0 
    | by apply: (typingcut (A:= (renInst (readE rho) A))); [ apply H0 | apply H1]
    |
    ].

    move => p c H2; 
           remember (f p) as d;
           move: Heqd (e p);
           elim: (f p);
           [ move => c0 _; by apply
           | move => H3; move: c H2; rewrite H3 => c Hc; inversion Hc
           ].

    move => p Delta H2; apply : (H0 p Delta) => //.
    simpl.
    rewrite /getA/getTerms; simpl.
    apply Lem56 => //.

    by elim: (H1) => _ [_ H2] /=;
    move: (H2 xn); clear H2;
    move : (rho.(readn) xn) => b H2; apply: typingselect;
    rewrite /Treadn;
    simpl;
    rewrite H2;
    move: (TCmapProp (renInst (readE rho))(renInst (readE rho)) Gamma) => [_ [_ H3]];
    rewrite H3;
    apply H0.
  Qed.

End LAFwEL.