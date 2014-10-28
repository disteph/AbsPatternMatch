Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion. 
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
        qLabSorting qLab : 
          forall Sigma (xq:qLab) s, SortingRel Sigma (asT xq) s <-> s = Sigma xq;
        renSorting qLab qLab' :
          forall (pi:qLab -> qLab') Sigma r s, 
            SortingRel (q:=get asQS) (comp Sigma pi) r s
            -> SortingRel (q:=get asQS) Sigma (lift2Terms pi r) s
      }.

  Canonical QSwE2QS `(QuantifyingStructureswE) := @QSwE2QS_base So Te SoR.

  Fixpoint renTList `{QuantifyingStructureswE}
           qLab qLab' l (pi:qLab -> qLab') (tl: TList qLab l) : TList qLab' l
  := match tl with
        | TermNil => TermNil _ _
        | TermCons so r l' tl' => TermCons so (lift2Terms pi r) (renTList pi tl')
    end.

  Definition renInst `{QuantifyingStructureswE}
             qLab qLab' (pi:qLab -> qLab')
             {A} (Alr: Inst A qLab): Inst A qLab'
    := [getA Alr,renTList pi (getTerms Alr)].

  Definition ContextswE `{QuantifyingStructureswE} wext A B C
    := Contexts wext A B C (fun qLab => (qLab:Type) -> C).

  Definition QSTwE2QST_base `(QSV:QuantifyingStructureswE) AtomV MoleculeV is_eqV: QSTypes :=
    {|
      QS := QSwE2QS QSV;
      Atom := AtomV;
      Molecule := MoleculeV;
      is_eq := is_eqV
    |}
  .

  Class QSTypeswE `(QSwE : QuantifyingStructureswE) AtomV MoleculeV is_eqV
    := 
      {
        asQSwE := QSwE;
        asQST := QSTwE2QST_base (QSV:=QSwE) (AtomV:=AtomV) MoleculeV is_eqV
      }.
  
  Coercion asQSwE: QSTypeswE >-> QuantifyingStructureswE.

  Canonical QSTwE2QST `(QSTypeswE)
    := QSTwE2QST_base (QSV:=QSwE) (AtomV:=AtomV) MoleculeV is_eqV.

  Context `(QSTV: QSTypeswE).

  Class TContextswE wext :=
    {
      TCstruct (qLab: QWorld _)
      : ContextswE wext
                 (Inst Atom qLab) 
                 (Inst Molecule qLab) 
                 (Sorts (QSwE2QS QSTV));
      TCmap qLab qLab' w :
        forall (f1: Inst Atom qLab -> Inst Atom qLab')
          (f2: Inst Molecule qLab -> Inst Molecule qLab'),
          ((TCstruct qLab).(Csupport) w)
          -> ((TCstruct qLab').(Csupport) w);
      TCren {w:World _} st: (w.(QLab):Type) -> (wext st w).(QLab);
      TCst  {w:World _} st: @Dec (wext st w).(QLab) unit unit st;
      TCrenProp {w:World _} 
                st 
                (Gamma:(TCstruct w.(QLab)).(Csupport) w)
                xq 
                Delta:
        readE (extends Delta Gamma)(TCren st xq) = readE Gamma xq
    }
  .

  Coercion TCstruct: TContextswE >-> Funclass.
  
  Definition InstTypingDec {qLab:QWorld _} {st ls}
             (qn : @Dec qLab unit unit st)
             (lq: TList qLab ls)
             (Delta:TypingDec st ls)
  : @Dec (Sorts (QSwE2QS QSTV)) (Inst Atom qLab) (Inst Molecule qLab) st.
  Proof.
    move:ls lq Delta.
    induction st => ls lq Delta; inversion Delta; inversion qn => //=.
                                                          exact (leafP([X,lq])).
    exact (leafN([X,lq])).
    exact (dummy).
    exact (node (IHst1 X1 ls lq X) (IHst2 X2 ls lq X0)).
    exact (qnode so (IHst X1 (so::ls) (TermCons so (asT X0) lq) X)).
  Defined.

  Definition TContextwE2TContext `(TCV: TContextswE wext) :=
    {|
      TCsupport w := TCV w.(QLab) w;
      Treadp w := readp (c := TCV w.(QLab)) (w:=w);
      Treadn w := readn (c := TCV w.(QLab)) (w:=w);
      TreadE w := readE (c := TCV w.(QLab)) (w:=w);
      Textends w st Deltal Gamma :=
        extends (st:=st) (c:=TCV (wext st w).(QLab))
                (InstTypingDec (qLab := (wext st w).(QLab)) 
                               (TCst (TContextswE := TCV) st) 
                               (renTList (TCren (TContextswE := TCV) st) (getTerms Deltal)) 
                               (getA Deltal))
                (TCmap (renInst
                          (TCren (TContextswE := TCV) st))
                       (renInst
                          (TCren (TContextswE := TCV) st)) Gamma)
    |}
  .

End LAFwE.

Definition LAFwE2LAF_base
          `{QSTV:QSTypeswE}
          {wext : DecStruct -> World _ -> World _} 
          (TCV: TContextswE _ wext) 
          {PatternsV PatDecV PatternsTypedV} :=
  {|
    QST := QSTwE2QST QSTV;
    wextends := wext;
    TContext := TContextwE2TContext TCV;
    Patterns := PatternsV;
    PatDec   := PatDecV;
    PatternsTyped := PatternsTypedV
  |}.

Class LAFswE `{QSTV:QSTypeswE} {wext PatternsV PatDecV PatternsTypedV} :=
  {
    asQSTwE := QSTV;
    TCV : TContextswE _ wext;
    asLAF := LAFwE2LAF_base (QSTV:=QSTV) (wext:=wext) 
                      TCV
                      (PatternsV:=PatternsV)
                      (PatDecV:=PatDecV)
                      (PatternsTypedV:=PatternsTypedV)
  }.

Coercion asQSTwE: LAFswE >-> QSTypeswE.

Canonical LAFwE2LAF `(LAFswE)
  := LAFwE2LAF_base (QSTV:=QSTV) (wext:=wext) TCV
                   (PatternsV:=PatternsV)
                   (PatDecV:=PatDecV)
                     (PatternsTypedV:=PatternsTypedV)
.

Print Canonical Projections.
Print Graph.


Definition Contlift `{QuantifyingStructureswE}{wext}{E F A B C D:Type}
           (RelQ: E -> F -> Prop)
           (RelP: A -> C -> Prop) 
           (RelN: B -> D -> Prop)
           {Context1 : ContextswE wext A B E}
           {Context2 : ContextswE wext C D F}
           {w} 
: Context1 w -> Context2 w -> Prop
  := fun Gamma rho =>
      (forall xq, RelQ (readE Gamma xq) (readE rho xq))
      /\ (forall xp, RelP (readp Gamma xp) (readp rho xp))
      /\ (forall xn, RelN (readn Gamma xn) (readn rho xn))
.

Definition GenericCorr `{QuantifyingStructureswE}{wext}{E F A B C D:Type} 
           (RelQ: E -> F -> Prop)
           (RelP: A -> C -> Prop)
           (RelN: B -> D -> Prop)
           {Context1 : ContextswE wext A B E}
           {Context2 : ContextswE wext C D F}
:= forall w st (Gamma:Context1 w) (rho:Context2 w) v Delta,
    Declift RelQ RelP RelN (st:=st) Delta v
    -> Contlift RelQ RelP RelN Gamma rho 
    -> Contlift RelQ RelP RelN (extends Delta Gamma) (extends v rho).



(*

Definition correctNaming {E A B C D:Type} {qVar st} (Sigma: qVar -> E) v nametree
  := Declift (st:=st) (A:=A) (B:=B) (C:=C) (D:=D)
             (fun s q => Sigma q = s)
             (fun _ _ => True)
             (fun _ _ => True)
             v nametree.
*)