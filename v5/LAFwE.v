Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion. 
Generalizable All Variables.
Typeclasses eauto := 5.

Require Import ssreflect List Basic LAF.

Definition comp {A B C} (g:B -> C) (f:A -> B) x := g(f x).

Section LAFwE.
  (*************************)
  (* Quantifying Structure *)
  (*************************)

  Canonical QSwE2QS So Te SoR: QuantifyingStructures :=
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
        asQS := QSwE2QS (So:=So) (Te:=Te) SoR;
        asT qLab : qLab -> Terms (q:=asQS) qLab;
        lift2Terms qLab qLab' : (qLab -> qLab') -> Terms (q:=asQS) qLab -> Terms (q:= asQS) qLab';
        qLabSorting qLab : 
          forall Sigma (xq:qLab) s, SortingRel Sigma (asT xq) s <-> s = Sigma xq;
        renSorting qLab qLab' :
          forall (pi:qLab -> qLab') Sigma r s, 
            SortingRel (q:=asQS) (comp Sigma pi) r s
            -> SortingRel (q:=asQS) Sigma (lift2Terms pi r) s
      }.

  Coercion asQS: QuantifyingStructureswE >-> QuantifyingStructures.

  Fixpoint renTList `(Q:QuantifyingStructureswE) qLab qLab' l (pi:qLab -> qLab')
  (tl: TList (QS:=Q) qLab l): TList (QS:=Q) qLab' l
  := match tl with
        | TermNil => TermNil _ _
        | TermCons so r l' tl' => TermCons so (lift2Terms pi r) (renTList pi tl')
    end.

  Definition renInst  `(Q:QuantifyingStructureswE) qLab qLab' (pi:qLab -> qLab')
  {A} (Alr: Inst A (QS:=Q) qLab): Inst A (QS:=Q) qLab'
    := [getA Alr,renTList pi (getTerms Alr)].

  Canonical QSTwE2QST `(QSV:QuantifyingStructureswE) AtomV MoleculeV is_eqV: QSTypes :=
    {|
      QS := QSV;
      Atom := AtomV;
      Molecule := MoleculeV;
      is_eq := is_eqV
    |}
  .

  Class QSTypeswE `{QSV:QuantifyingStructureswE} {AtomV MoleculeV is_eqV} := 
    {
      asQSwE := QSV;
      asQST := QSTwE2QST (QSV:=QSV) (AtomV:=AtomV) MoleculeV is_eqV
    }.

  Coercion asQST: QSTypeswE >-> QSTypes.
  (* Coercion asQSwE: QSTypeswE >-> QuantifyingStructureswE. *)

  Context `(QSTV: QSTypeswE).

  Class TContextswE wext :=
    {
      TCstruct (qLab: QWorld QSTV)
      : Contexts (QS := QSTV) wext
                 (Inst Atom qLab) 
                 (Inst Molecule qLab) 
                 (Terms qLab)
                 SoContexts;
      TCmap qLab qLab' w :
        forall (f1: Inst Atom qLab -> Inst Atom qLab')
          (f2: Inst Molecule qLab -> Inst Molecule qLab'),
          ((TCstruct qLab).(Csupport) w)
          -> ((TCstruct qLab').(Csupport) w);
      TCren {w:World QSTV} st: w.(QLab) -> (wext st w).(QLab);
      TCst  {w:World QSTV} st: @Dec (wext st w).(QLab) unit unit st;
      TCrenProp {w:World QSTV} 
                st 
                (Gamma:(TCstruct w.(QLab)).(Csupport) w)
                xq 
                Delta:
        readE (extends Delta Gamma)(TCren st xq) = readE Gamma xq
    }
  .

  Coercion TCstruct: TContextswE >-> Funclass.
  
  Definition InstTypingDec {qLab:QWorld QSTV} {st ls}
             (qn : @Dec qLab unit unit st)
             (lq: TList qLab ls)
             (Delta:TypingDec st ls)
  : @Dec (Terms qLab) (Inst Atom qLab) (Inst Molecule qLab) st.
  Proof.
    move:ls lq Delta.
    induction st => ls lq Delta; inversion Delta; inversion qn => //=.
                                                          exact (leafP([X,lq])).
    exact (leafN([X,lq])).
    exact (dummy).
    exact (node (IHst1 X1 ls lq X) (IHst2 X2 ls lq X0)).
    exact (qnode (asT X0) (IHst X1 (so::ls) (TermCons so (asT X0) lq) X)).
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

Canonical LAFwE2LAF
          `{QSTV:QSTypeswE}
          {wext : DecStruct -> World QSTV -> World QSTV} 
          (TCV: TContextswE (QSTV:=QSTV) wext) 
          {PatternsV PatDecV PatternsTypedV} :=
  {|
    QST := QSTV;
    wextends := wext;
    TContext := TContextwE2TContext TCV;
    Patterns := PatternsV;
    PatDec   := PatDecV;
    PatternsTyped := PatternsTypedV
  |}.

Class LAFswE `{QSTV:QSTypeswE} 
          {wext : DecStruct -> World QSTV -> World QSTV} 
          (TCV: TContextswE (QSTV:=QSTV) wext) 
          {PatternsV PatDecV PatternsTypedV} :=
  {
    asQSTwE := QSTV;
    asLAF := LAFwE2LAF (QSTV:=QSTV) (wext:=wext) 
                      TCV
                      (PatternsV:=PatternsV)
                      (PatDecV:=PatDecV)
                      (PatternsTypedV:=PatternsTypedV)
  }.

Coercion asLAF: LAFswE >-> LAFs.

Print Graph.


(*

(* In ContextType, we have an implementation of operations about
contexts:

- extends is the way to extend a context, thanks to a CAB-@Dec.

- corr is a property required of extensions:

if rho and Gamma are "RelP-RelN-related" (the values to which a variable is
mapped by rho and Gamma are RelP/RelN-related), and v and Delta are
"RelP-RelN-related" (as @Decs), then the extension of rho by v and the
extension of Gamma by Delta are "RelP-RelN-related".

*)


Definition correctNaming {E A B C D:Type} {qVar st} (Sigma: qVar -> E) v nametree
  := Declift (st:=st) (A:=A) (B:=B) (C:=C) (D:=D)
             (fun s q => Sigma q = s)
             (fun _ _ => True)
             (fun _ _ => True)
             v nametree.



  Definition Contlift {E F A B C D:Type}
             (RelQ: E -> F -> Prop)
             (RelP: A -> C -> Prop) 
             (RelN: B -> D -> Prop)
             {w} 
  : @Contexts E A B w -> @Contexts F C D w -> Prop
    := fun Gamma rho =>
        (forall xq, RelQ (Gamma.(readq) xq) (readq rho xq))
        /\ (forall xp, RelP (Gamma.(readp) xp) (rho.(readp) xp))
        /\ (forall xn, RelN (Gamma.(readn) xn) (rho.(readn) xn))
  .


    corr {E F A B C D: Type} {w:World} {st} : 
      forall (RelQ: E -> F -> Prop)
        (RelP: A -> C -> Prop)
        (RelN: B -> D -> Prop)
        (rho:@ContType E A B w)
        (Gamma:@ContType F C D w)
        v Delta,
        Declift RelQ RelP RelN (st:=st) v Delta
        -> Contlift RelQ RelP RelN rho Gamma
        -> Contlift RelQ RelP RelN (extends v rho) (extends Delta Gamma);



*)