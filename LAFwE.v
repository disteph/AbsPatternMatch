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

        qLabSorting qLab : 
          forall Sigma (xq:qLab) s, SortingRel Sigma (asT xq) s <-> s = Sigma xq;

        renSorting qLab qLab' :
          forall (pi:qLab -> qLab') Sigma r s, 
            SortingRel (q:=get asQS) (comp Sigma pi) r s
            -> SortingRel (q:=get asQS) Sigma (lift2Terms pi r) s;

        wextendsE : DecStruct -> World (get asQS) -> World (get asQS);
        Extren {w:World (get asQS)} st: (w.(QLab):Type) -> ((wextendsE st w).(QLab):Type);
        Extst  {w:World (get asQS)} st: @Dec (wextendsE st w).(QLab) unit unit st
      }.

  Canonical QSwE2QS `(QuantifyingStructureswE) := @QSwE2QS_base So Te SoR.

  (* Renaming in term lists and instantiated things *)

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

  (* Stuff about generic contexts *)

  Definition ContextswE `{QuantifyingStructureswE} A B C
    := Contexts wextendsE A B C (fun qLab => (qLab:Type) -> C).

  Definition renProp
             `{QuantifyingStructureswE} 
             `(Cont: ContextswE A B C)
    := forall w st (Gamma:Cont w) Delta xq, 
        readE (extends Delta Gamma)(Extren st xq) = readE Gamma xq.

  Definition stProp
             `{QuantifyingStructureswE} 
             `(Cont: ContextswE A B C)
    := forall w st (Gamma:Cont w) Delta,
        Declift (fun s xq => readE (extends Delta Gamma) xq = s)
                (fun _ _ => True)
                (fun _ _ => True)
                Delta (Extst st).

  Definition Contlift `{QuantifyingStructureswE}{E F A B C D:Type}
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

  Definition ContMap `{QuantifyingStructureswE}{E F A B C D:Type}
             (fQ: E -> F)
             (fP: A -> C)
             (fN: B -> D)
             {Context1 : ContextswE A B E}
             {Context2 : ContextswE C D F}
             {w} 
  : Context1 w -> Context2 w -> Prop
    := Contlift (fun c c' => c' = fQ c) (fun c c' => c' = fP c) (fun c c' => c' = fN c).

  (* Enriching Quantifying structures with types (instantiated atoms
  and molecules), now with eigenvariables *)

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
      : ContMap (fun i => i) f1 f2 Gamma (TCmap f1 f2 Gamma);

      TCrenProp qLab : renProp (TCstruct qLab);
      TCstProp qLab : stProp (TCstruct qLab)
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


Definition GenericCorr `{QuantifyingStructureswE}{E F A B C D:Type} 
           (RelQ: E -> F -> Prop)
           (RelP: A -> C -> Prop)
           (RelN: B -> D -> Prop)
           {Context1 : ContextswE A B E}
           {Context2 : ContextswE C D F}
:= forall w st (Gamma:Context1 w) (rho:Context2 w) v Delta,
    Declift RelQ RelP RelN (st:=st) Delta v
    -> Contlift RelQ RelP RelN Gamma rho 
    -> Contlift RelQ RelP RelN (extends Delta Gamma) (extends v rho).
