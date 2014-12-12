Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.
Typeclasses eauto := 1.

Require Import ssreflect List Basic LAF.

Definition comp {A B C} (g:B -> C) (f:A -> B) x := g(f x).

Section LAFwE.
  (*************************)
  (* Quantifying Structure *)
  (*************************)

  Definition QSwE2QS_base So Te SoR : QuantifyingStructures :=
    {|
      Sorts := So;
      QWorld := Type;
      Terms := Te;
      SoContexts qLab := qLab -> So;
      SortingRel := SoR
    |}
  .

  Class QuantifyingStructureswE {So Te SoR}
    := 
      {
        asQS: SClass (@QSwE2QS_base So Te SoR);

        asT (qLab: QWorld (get asQS)): qLab -> Terms qLab;

        lift2Terms qLab qLab' 
        : (qLab -> qLab') -> Terms (q:= get asQS) qLab -> Terms (q:= get asQS) qLab';

        lift2Terms_asT qLab qLab' (f:qLab -> qLab')
        : forall xq:qLab, lift2Terms f (asT xq) = asT (f xq);

        lift2Terms_comp qLab0 qLab1 qLab2
                        (f1:qLab0 -> qLab1)
                        (f2:qLab1 -> qLab2)
                        (f3:qLab0 -> qLab2)
        : (forall xq:qLab0, f3 xq = f2(f1 xq))
          -> (forall t:Terms (q:= get asQS) qLab0, lift2Terms f3 t = lift2Terms f2(lift2Terms f1 t));

        qLabSorting qLab : 
          forall Sigma (xq:qLab) s, SortingRel Sigma (asT xq) s <-> s = Sigma xq;

        renSorting qLab qLab' :
          forall (pi:qLab -> qLab') Sigma Sigma' r s, 
            (forall xq, Sigma(pi xq) = Sigma' xq)
            -> SortingRel (q:=get asQS) Sigma' r s
            -> SortingRel (q:=get asQS) Sigma (lift2Terms pi r) s;

        wextendsE : DecStruct -> World (get asQS) -> World (get asQS)
      }.

  Canonical QSwE2QS `(QuantifyingStructureswE) := @QSwE2QS_base So Te SoR.

  (* Renaming in term lists and instantiated things *)

  Fixpoint renTList `{QuantifyingStructureswE}
           qLab qLab' l (pi:qLab -> qLab') (tl: TList qLab l) : TList qLab' l
  := match tl with
        | TermNil => TermNil _ _
        | TermCons so r l' tl' => TermCons so (lift2Terms pi r) (renTList pi tl')
    end.

  Lemma renTList_comp `{QuantifyingStructureswE} qLab0 qLab1 qLab2
        (f1:qLab0 -> qLab1)
        (f2:qLab1 -> qLab2)
        (f3:qLab0 -> qLab2)
        ls
  : (forall xq:qLab0, f3 xq = f2(f1 xq))
    -> (forall tl:TList qLab0 ls, renTList f3 tl = renTList f2(renTList f1 tl)).
  Proof.
    move => H0.
    elim => //.
    move => s head l tail IH /=.
    rewrite IH (lift2Terms_comp (qLab1 := qLab1) (f1 := f1) (f2 := f2) _ head) => //.
  Qed.

  Definition renInst `{QuantifyingStructureswE}
             qLab qLab' (pi:qLab -> qLab')
             {A} (Alr: Inst A qLab): Inst A qLab'
    := [getA Alr,renTList pi (getTerms Alr)].

  Lemma renInst_comp `{QuantifyingStructureswE} qLab0 qLab1 qLab2
        (f1:qLab0 -> qLab1)
        (f2:qLab1 -> qLab2)
        (f3:qLab0 -> qLab2)
        A
  : (forall xq:qLab0, f3 xq = f2(f1 xq))
    -> (forall Alr: Inst A qLab0, renInst f3 Alr = renInst f2(renInst f1 Alr)).
  Proof.
    move => H0.
    elim => //.
    move => x p /=.
    rewrite /renInst /= (renTList_comp (qLab1 := qLab1) (f1 := f1) (f2 := f2)) => //.
  Qed.

  (* Enriching Quantifying structures with types (instantiated atoms
  and molecules), now with eigenvariables *)

  Definition QSTwE2QST_base `(QSV:QuantifyingStructureswE) AtomV MoleculeV is_eqV: QSTypes :=
    {|
      QS := QSwE2QS _;
      Atom := AtomV;
      Molecule := MoleculeV;
      is_eq := is_eqV
    |}
  .

  Class QSTypeswE `(QSwE : QuantifyingStructureswE) AtomV MoleculeV is_eqV
    := 
      {
        Extren {w:World (get asQS)} st: (w.(QLab):Type) -> ((wextendsE st w).(QLab):Type);
        Extst  {w:World (get asQS)} st: @Dec (wextendsE st w).(QLab) unit unit st;
        asQSwE := QSwE;
        asQST := QSTwE2QST_base (QSV:=QSwE) (AtomV:=AtomV) MoleculeV is_eqV;
        is_eq_ren {qLab qLab'} 
        : forall IA IA' : Inst (Atom (q:=asQST)) qLab,
            is_eq IA IA'
            -> forall pi:qLab -> qLab', is_eq (q:=asQST) (renInst pi IA) (renInst pi IA')
      }.
  
  Coercion asQSwE: QSTypeswE >-> QuantifyingStructureswE.

  Canonical QSTwE2QST `(QSTypeswE)
    := QSTwE2QST_base (QSV:=QSwE) (AtomV:=AtomV) MoleculeV is_eqV.

  (* Stuff about generic contexts *)

  Definition ContextswE `{QuantifyingStructureswE} A B C
    := Contexts wextendsE A B C (fun qLab => (qLab:Type) -> C).

  Definition renProp
             `{QSTypeswE} 
             `(Cont: ContextswE A B C)
    := forall w st (Gamma:Cont w) Delta xq, 
        readE (extends Delta Gamma)(Extren st xq) = readE Gamma xq.

  Definition stProp
             `{QSTypeswE} 
             `(Cont: ContextswE A B C)
    := forall w st (Gamma:Cont w) Delta,
        Declift (fun s xq => s = readE (extends Delta Gamma) xq)
                (fun _ _ => True)
                (fun _ _ => True)
                Delta (Extst st).

  Definition Contlift `{QSTypeswE}{E F A B C D:Type}
             (RelQ: E -> F -> Prop)
             (RelP: A -> C -> Prop)
             (RelN: B -> D -> Prop)
             {Context1 : ContextswE A B E}
             {Context2 : ContextswE C D F}
             {w} 
  : Context1 w -> Context2 w -> Prop
    := fun Gamma rho =>
        (forall xq, RelQ (readE Gamma xq) (readE rho xq))
        /\ (forall xp, RelP (readp Gamma xp) (readp rho xp))
        /\ (forall xn, RelN (readn Gamma xn) (readn rho xn))
  .

  Definition ContMap `{QSTypeswE}{E F A B C D:Type}
             (fQ: E -> F)
             (fP: A -> C)
             (fN: B -> D)
             {Context1 : ContextswE A B E}
             {Context2 : ContextswE C D F}
             {w} 
  : Context1 w -> Context2 w -> Prop
    := Contlift (fun c c' => c' = fQ c) (fun c c' => c' = fP c) (fun c c' => c' = fN c).

  (* Now we define typing contexts in the sense of LAF with eigenvariables *)

  Context `(QSTV: QSTypeswE).

  Class TContextswE :=
    {
      TCstruct (qLab: QWorld (QSTwE2QST QSTV))
      : ContextswE (Inst Atom qLab) 
                   (Inst Molecule qLab) 
                   (Sorts (QSwE2QS QSTV));

      TCmap (qLab qLab': QWorld (QSTwE2QST QSTV)) w :
        forall (f1: Inst Atom qLab -> Inst Atom qLab')
          (f2: Inst Molecule qLab -> Inst Molecule qLab'),
          ((TCstruct qLab).(Csupport) w)
          -> ((TCstruct qLab').(Csupport) w);

      TCmapProp qLab qLab' w
                (f1: Inst Atom qLab -> Inst Atom qLab')
                (f2: Inst Molecule qLab -> Inst Molecule qLab')
                (Gamma: TCstruct qLab w)
      : ContMap (fun i => i) f1 f2 Gamma (TCmap f1 f2 Gamma)
    }
  .

  Coercion TCstruct: TContextswE >-> Funclass.
  
  Definition InstTypingDec {qLab:QWorld _} {st ls}
             (qn : @Dec qLab unit unit st)
             (lq: TList qLab ls)
             (Delta:TypingDec st ls)
  : @Dec (Sorts (QSwE2QS QSTV)) (Inst Atom qLab) (Inst Molecule qLab) st.
  Proof.
    induction Delta.
    exact (leafP([a,lq])).
    exact (leafN([m,lq])).
    exact (dummy).
    inversion qn.
    exact (node (IHDelta1 X lq) (IHDelta2 X0 lq)).
    inversion qn.
    exact (qnode so (IHDelta X0 (TermCons so (asT X) lq))).
  Defined.

  Coercion TContextwE2TContext `(TCV: TContextswE) :=
    {|
      TCsupport w := TCV w.(QLab) w;
      Treadp w := readp (c := TCV w.(QLab)) (w:=w);
      Treadn w := readn (c := TCV w.(QLab)) (w:=w);
      TreadE w := readE (c := TCV w.(QLab)) (w:=w);
      Textends w st Deltal Gamma :=
        extends (st:=st) (c:=TCV (wextendsE st w).(QLab))
                (InstTypingDec (qLab := (wextendsE st w).(QLab)) 
                               (Extst st) 
                               (renTList (Extren st) (getTerms Deltal)) 
                               (getA Deltal))
                (TCmap (renInst (Extren st)) (renInst (Extren st)) Gamma)
    |}
  .

End LAFwE.

Definition LAFwE2LAF_base
          `{QSTV:QSTypeswE}
          (TCV: TContextswE _) 
          {PatternsV PatDecV PatternsTypedV} :=
  {|
    QST := QSTwE2QST QSTV;
    wextends := wextendsE;
    TContext := TCV;
    Patterns := PatternsV;
    PatDec   := PatDecV;
    PatternsTyped := PatternsTypedV
  |}.

Class LAFswE `{QSTV:QSTypeswE} {PatternsV PatDecV PatternsTypedV} :=
  {
    asQSTwE := QSTV;
    TCV : TContextswE _;
    asLAF := LAFwE2LAF_base (QSTV:=QSTV)
                      TCV
                      (PatternsV:=PatternsV)
                      (PatDecV:=PatDecV)
                      (PatternsTypedV:=PatternsTypedV)
  }.

Coercion asQSTwE: LAFswE >-> QSTypeswE.

Canonical LAFwE2LAF `(LAFswE)
  := LAFwE2LAF_base (QSTV:=QSTV) TCV
                   (PatternsV:=PatternsV)
                   (PatDecV:=PatDecV)
                   (PatternsTypedV:=PatternsTypedV)
.


Definition GenericCorr `{QSTypeswE}{E F A B C D:Type} 
           (RelQ: E -> F -> Prop)
           (RelP: A -> C -> Prop)
           (RelN: B -> D -> Prop)
           {Context1 : ContextswE A B E}
           {Context2 : ContextswE C D F}
:= forall w st (Gamma:Context1 w) (rho:Context2 w) v Delta,
    Declift RelQ RelP RelN (st:=st) Delta v
    -> Contlift RelQ RelP RelN Gamma rho 
    -> Contlift RelQ RelP RelN (extends Delta Gamma) (extends v rho).
