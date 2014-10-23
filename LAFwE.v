Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion. 

Require Import ssreflect List Basic LAF.

Definition comp {A B C} (g:B -> C) (f:A -> B) x := g(f x).

(*************************)
(* Quantifying Structure *)
(*************************)

Record QuantifyingStructureswE := 
  {
    SortsE : Type;
    TermsE : Type -> Type;
    asT qLab : qLab -> TermsE qLab;
    lift2Terms qLab qLab' : (qLab -> qLab') -> TermsE qLab -> TermsE qLab';
    SortingRelE qLab : (qLab -> SortsE) -> TermsE qLab -> SortsE -> Prop;
    qLabSorting qLab : 
      forall Sigma (xq:qLab) s, SortingRelE Sigma (asT xq) s <-> s = Sigma xq;
    renSorting qLab qLab' :
      forall (pi:qLab -> qLab') Sigma r s, 
        SortingRelE (comp Sigma pi) r s
        -> SortingRelE Sigma (lift2Terms pi r) s
  }.

Coercion QSwE2QS QS: QuantifyingStructures :=
  {|
    Sorts := QS.(SortsE);
    QWorld := Type;
    Terms := QS.(TermsE);
    SoContexts qLab := qLab -> QS.(SortsE);
    SortingRel := QS.(@SortingRelE)
  |}
.


(* Definition namedTypingDec {st ls}  *)
(*            (lq: UTTermList Term ls) *)
(*            (Delta:TypingDec st ls)  *)
(*            (qn : @Dec unit unit unit st) *)
(* : @Dec Sorts (Par Atom) (Par Molecule) st. *)
(* Proof. *)
(*   move:ls lq Delta. *)
(*   induction st => ls lq Delta; inversion Delta; inversion qn => //=. *)
(*   exact (leafP([X,lq])). *)
(*   exact (leafN([X,lq])). *)
(*   exact (dummy). *)
(*   exact (node (IHst1 X1 ls lq X) (IHst2 X2 ls lq X0)). *)
(*   exact (qnode so (IHst X1 (so::ls) (TermCons (Term.(varTerm) X0) (Logic.I) lq) X)). *)
(* Defined. *)


Section LAF.

  (*********)
  (* TYPES *)
  (*********)

  (* The language of types is given by 
- Sorts:    sorts for terms
- Atom:     type of atoms
- Molecule: type of molecules *)

  Record QSTypes :=
    {
      QS :> QuantifyingStructures;
      Atom        : list QS.(@Sorts) -> Type;
      Molecule    : list QS.(@Sorts) -> Type;
      is_eq {qLab}: (Inst Atom qLab) -> (Inst Atom qLab) -> Prop
    }.

  Arguments Atom {_} _.
  Arguments Molecule {_} _.

  (* Variable QST: QSTypes. *)

  Inductive TypingDec {QST: QSTypes}: DecStruct -> list QST.(@Sorts) -> Type  :=
  | TleafP : forall {l}, Atom l -> TypingDec sleafP l
  | TleafN : forall {l}, Molecule l -> TypingDec sleafN l
  | Tdummy : forall {l}, TypingDec sdummy l
  | Tnode  : forall {l s1 s2}, TypingDec s1 l -> TypingDec s2 l -> TypingDec (snode s1 s2) l
  | Tqnode : forall {l s} so, TypingDec s (so::l) -> TypingDec (sqnode s) l.

  (************)
  (* Contexts *)
  (************)

  (* Axiomatic specification for the implementation of contexts:

Contexts can be typing contexts (variables are mapped to "types"), or
substitutions (variables are mapped to "terms").

Contexts map quantifiable, positive and negative variables to elements
of C, A and B, respectively.
readq, readp and readn are for reading the values.
   *)

  Record World {QS} :=
    {
      PLab:Type;
      NLab:Type;
      QLab:QS.(QWorld)
    }.

  (* A typing context maps positive variables atoms and negative variables to molecules *)

  Record TypingContexts (QST:QSTypes)(wextends: DecStruct -> @World QST -> @World QST) := 
    {
      TCsupport w :> Type;
      Treadp {w} : TCsupport w -> w.(PLab) -> Inst Atom w.(QLab);
      Treadn {w} : TCsupport w -> w.(NLab) -> Inst Molecule w.(QLab);
      TreadE {w} : TCsupport w -> SoContexts w.(QLab);
      Textends {w st}: 
        forall v : Inst (TypingDec st) w.(QLab), TCsupport w -> TCsupport (wextends st w)
    }.

  Arguments Textends {QST wextends t w st} _ _.

  (* The language of proof-terms is parameterised by:
- Patterns: type of elements that can be thought as patterns
To each pattern p is associated a tree skeleton PatDec p
   *)

  Record LAFs :=
    {
      QST:> QSTypes;
      wextends : DecStruct -> @World QST -> @World QST;
      TContext : TypingContexts QST wextends;
      Patterns : Type;
      PatDec   : Patterns -> DecStruct;
      PatternsTyped (p:Patterns) l : @TypingDec QST (PatDec p) l -> Molecule l -> Prop
    }.

End LAF.

Notation "x =cis= y" := (cexists_as _ x y) (at level 30, right associativity).



(*


Definition Contmap {A B C D:Type}
           (fP: A -> C) 
           (fN: B -> D)
           {w} 
: @ContType E A B w -> @ContType F C D w
  := fun Gamma => 
      {| readq := fun xq => fQ (Gamma.(readq) xq);
         readp := fun xp => fP (Gamma.(readp) xp);
         readn := fun xn => fN (Gamma.(readn) xn)
      |}
.

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

Record ContextType := 
  {
    wextends: DecStruct -> World -> World;

    extends {C A B : Type} {w:World} {st}: 
      forall v : @Dec C A B st, @ContType C A B w -> @ContType C A B (wextends st w);

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

    qinject st w : w.(QVar) -> (wextends st w).(QVar);
    extends_qinject {C A B : Type} {w:World} {st} xq:
      forall (v: @Dec C A B st) rho, (extends v rho).(readq) (qinject st w xq) = rho.(readq) xq;

    qnew    st w : @Dec (wextends st w).(QVar) unit unit st;
    extends_qnew {C A B : Type} {w:World} {st}:
      forall (v: @Dec C A B st) rho, correctNaming (extends v rho).(readq) v (qnew st w)
  }
.





Record QRenamable :=
  { QRenamablesupport :> Type -> Type;
    qrename {QVar1 QVar2}
    : (QVar1 -> QVar2) -> (QRenamablesupport QVar1 -> QRenamablesupport QVar2)
  }.

Record TermAlgebra :=
  {
    TermSet :> QRenamable;
    varTerm {qVar} : qVar -> TermSet qVar;
    varTermRename {qVar qVar' xq}: 
      forall (ren: qVar -> qVar'),
        varTerm (ren xq) = TermSet.(qrename) ren (varTerm xq)
  }
.

Variable Term : TermAlgebra.


Fixpoint UTTermListRen {qVar qVar' l} (ren:qVar -> qVar') (tl:UTTermList (Term qVar) l)
: UTTermList (Term qVar') l :=
  match tl with
      | TermNil => TermNil
      | TermCons r _ _ _ tl' => TermCons (Term.(qrename) ren r)
                                        (Logic.I) 
                                        (UTTermListRen ren tl')
  end.

Definition InstRen {A qVar qVar'} (ren:qVar -> qVar') (x:Inst A qVar) :=
  match x with
    | existS _ (a,tl) => [a,UTTermListRen ren tl]
  end.

Definition Textends {w st l} Delta Gamma (tl:UTTermList (Term w.(QVar)) l)
  := Context.(extends) (namedTypingDec (UTTermListRen (Context.(qinject) st w) tl)
                                     Delta
                                     (Context.(qnew) st w)
                      )
                      (Contmap (w := w)
                               (fun i => i)
                               (InstRen (Context.(qinject) st w))
                               (InstRen (Context.(qinject) st w))
                               Gamma
                      )
.

*)