Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Open Scope type_scope.

Require Import ssreflect LAF Semantics NormalisationTheory Basic.

Section HeadReduction.

  Context (LAF:LAFs).

  Definition WDep A := {w: World LAF & A w}.

  Record AbstractMachines :=
    {
      ETerms : Type;
      ESoContexts: LAF.(QWorld) -> Type;
      EPos   : Type;
      ENeg   : Type;
      Closures: World LAF -> Type;
      EContext: Contexts wextends EPos (ENeg + WDep Closures) ETerms ESoContexts;
      clNeg w : (Neg w * EContext w) -> Closures w;
      clNegInj : forall w cl1 cl2, @clNeg w cl1 = @clNeg w cl2 -> cl1 = cl2;
      EvalTerms {qLab} : ESoContexts qLab -> Terms qLab -> ETerms
    }
  .

  Notation "<< x , y >>" := (inr {{ _ , (clNeg (x,y)) }} ).
  Notation "<< x | y >>" := (existS (fun w => Command w * EContext _ w) _ (x,y)).

  Section AbstractMachines.

    Variable AM: AbstractMachines.

    Definition VNeg := sum AM.(ENeg) (WDep AM.(Closures)).

    Definition ECommand := WDep (fun w => Command w * EContext AM w).

    Definition EDec := @Dec AM.(ETerms) AM.(EPos) VNeg.

    Lemma EvalDec : 
      forall w (rho:AM.(EContext) w) st, TermDec w st ->  EDec st.
    Proof.
      move => w rho.
      elim => [v | v | v | s1 H1 s2 H2 v | s H v]; inversion v =>//=.
      exact (leafP (rho.(readp) X)).
      exact (leafN(<< X , rho >>)).
      exact dummy.
      exact (node (H1 X)(H2 X0)).
      exact (qnode (EvalTerms (readE rho) X) (H X0)).
    Defined.
    Unset Implicit Arguments.

    Definition ETriple := VNeg * {p:Patterns LAF & EDec (PatDec p)}.

    Set Implicit Arguments.
    Unset Strict Implicit.
    Set Maximal Implicit Insertion.

    Notation "<< x | y | z >>" := (x, {{ y,z }}).

    Inductive ECom2ETri : ECommand ->  ETriple -> Prop :=
    | head1:
        forall w (xn:w.(NLab)) p d rho,
          ECom2ETri << select xn (pos p d) | rho >> << readn rho xn | p | EvalDec rho d >>
    | head2:
        forall w (tn:Neg w) p d rho,
          ECom2ETri << cut tn (pos p d) | rho >> <<<< tn,rho >>| p | EvalDec rho d >>
    .

    Inductive ETri2ECom : ETriple ->  ECommand -> Prop :=
    | head3:
        forall w (f:Reifiable w) p d rho c,
          f p =cis= c
          -> ETri2ECom <<<< rei f,rho >> | p | d >> << c | extends d rho >>
    .

    Lemma ETri2EComRed : forall w (f:Reifiable w) p d rho x,
                           ETri2ECom <<<< rei f,rho >> | p | d >> x
                           -> forall c, f p =cis= c
                               -> x = << c | extends d rho >>.
    Proof.
      move => w f p d rho x H.
      have: (forall f' rho', 
               clNeg(rei f,rho) = clNeg (rei f',rho')
               -> forall c' : Command _ (LAF:=LAF),
                   f' p =cis= c' ->
                   x =
                   {{ wextends (l:=LAF) (PatDec (l:=LAF) p) w,
                     (c', extends (c:=EContext AM) (w:=w) d rho')}}).
      refine
        (match H as J in ETri2ECom K K' 
               return 
               (match K with
                  | (inr {{ _ , closure }}, {{ p', d'}})
                    => forall f' rho', 
                        closure = clNeg (rei f',rho')
                        -> forall c', 
                            f' p' =cis= c'
                            -> K' =<< c' | extends d' rho' >>
                  | _ => True 
                end : Prop) with
           | head3 _ _ _ _ _ _ _ => _
         end)
      .
      move => f' rho' H0 c' H1.
      move:(clNegInj H0); clear H0 H; move => [H H0].
      rewrite H0;clear H0.
      inversion c0; clear c0.
      rewrite H in H2;clear H.
      inversion H1; clear H1.
      rewrite <- H2 in H3; clear H2.
      inversion H3; clear H3.
      rewrite H0 in H1; clear H0.
      rewrite H4 in H1; clear H4.
      rewrite H1.
      done.
      apply.
      done.
    Qed.

    Inductive HeadReduction : ETriple ->  ETriple -> Prop :=
    | head123 a b c : ETri2ECom a b -> ECom2ETri b c -> HeadReduction a c.

    Section Normalisation.

      Definition HeadStruct := 
        {|
          STerms   := ETerms AM;
          Valuations := ESoContexts AM;
          SLab     := EPos AM;
          SPos     := { p:Patterns LAF & EDec (PatDec p)};
          SNeg     := VNeg;
          orth     := SN HeadReduction ;
          SContexts := EContext AM;
          tild p v := {{ p, v }};
          SemTerms := @EvalTerms AM;
          I w rho f := << rei f, rho >>
        |}
      .

      Variable WF: well_founded (relation (LAF:=LAF)).

      Definition HeadRAlg :=
        {|
          modelStructure := HeadStruct;
          welf := WF;
          SemSorts s r := True;
          SemSoCont w Sigma sigma := True;
          SemSoCompat qLab Sigma r s sigma := fun _ _ => Logic.I;
          SemAtom a tl vp := True;
          SemAtom_eq qLab sigma a b tl := fun _ _ => Logic.I
        |}.

      Lemma SemEvalDec {w} : forall rho st (v:TermDec w st), 
                               SemDec (M:= HeadStruct) rho v = EvalDec rho v.
      Proof.
        move => rho.
        elim => [v | v | v | s1 H1 s2 H2 v | s H v]; dependent inversion v =>//=.
                                                    by elim n.
          by rewrite H1 H2.
            by rewrite H.
      Qed.

      Lemma Rem61 : forall w (c:Command w) rho, ECom2ETri << c | rho >> (SemC (M:= HeadStruct) rho c).
      Proof.
        move => w [[f] | xn]; move => [p v] rho /=; rewrite SemEvalDec.
        apply: head2.
        apply: head1.
      Qed.

      Lemma Rem61' : forall w (c:Command w) rho x, 
                       ECom2ETri << c | rho >> x
                                        -> x = (SemC (M:= HeadStruct) rho c).
      Proof.
        move => w [[f] | xn]; move => [p v] rho x /=; rewrite SemEvalDec => H.
        refine
          (match H as J in ECom2ETri K K' 
                 return 
                 (match K with
                    | {{ w', (cut tn' (pos p' v'), rho') }} 
                      => K' = << << tn', rho' >> | p' | EvalDec rho' v' >>
                    | {{ w', (_, rho') }} => True 
                  end : Prop) with
             | head1 _ _ _ _ _ => Logic.I
             | head2 _ _ _ _ _ => eq_refl
           end)
        .
        refine (match H as J in ECom2ETri K K' 
                      return 
                      (match K with
                         | {{ w', (select xn' (pos p' v'), rho') }} 
                           => K' = << readn (c:=EContext AM) (w:=w') rho' xn' | p' | EvalDec rho' v' >>
                         | {{ w', (_, rho') }} => True 
                       end : Prop) with
                  | head1 _ _ _ _ _ => eq_refl
                  | head2 _ _ _ _ _ => Logic.I
                end)
        .
      Qed.



      Lemma StabHN w :
        forall (f: Reifiable w) (rho: HeadRAlg.(SContexts) w) (p: Patterns LAF)
          l Delta (tl:STList HeadRAlg l) (v: SDec (PatDec p)) c,
          f p =cis= c
          -> SemTDec Delta tl v
          -> orth (SemC (extends v rho) c)
          -> orth (I rho f, tild p v).
      Proof.
        move => /= f rho p l Delta tl v c H0 _ H2.
        apply toSN => x' H3.
        inversion H3.
        clear a c0 H3 H4 H5.
        move: (ETri2EComRed H H0).
        clear H => H.
        rewrite H in H1; clear H H0 b.
        case: c H1 H2 => [[f'] | xn] ; move => [p' v'] /= ; rewrite SemEvalDec => H1 H2;
          move: (Rem61' H1); clear H1 => H1;
          rewrite H1 => /=; rewrite SemEvalDec => //.
      Qed.

      Variable TC: forall w st (rho:HeadRAlg.(SContexts) w) Gamma l (Delta:TypingDec st l) tl v, 
                     SemCont Gamma rho
                     -> SemTDec Delta (SemTermList (readE rho) tl) v
                     -> SemCont (Textends [Delta,tl] Gamma) (extends v rho).
      
      Definition HeadModel := 
        {|
          M0 := HeadRAlg;
          TypingCorr := @TC;
          Stability  := @StabHN
        |}.

      Theorem HeadNormalisation: 
        forall w Gamma c (rho: HeadModel.(SContexts) w),
          CommandTyping Gamma c -> SemCont Gamma rho -> SN HeadReduction (SemC rho c).
      Proof.
        move => w Gamma c rho H H1.
        elim: (adequacy HeadModel Gamma) => [_ [_ [_ [_ H']]]]. 
          by move:(H' c H rho H1).
      Qed.

    End Normalisation.
  End AbstractMachines.

  Section SyntacticMachines.

    Definition asAbstractMachine (w0 : World LAF)
               ClosuresV EContextV clNegV clNegInjV EvalTermsV :=
      {|
        ETerms    := Terms w0.(QLab);
        ESoContexts := SoContexts;
        EPos      := PLab w0;
        ENeg      := NLab w0;
        Closures  := ClosuresV;
        EContext  := EContextV;
        clNeg     := clNegV;
        clNegInj  := clNegInjV;
        EvalTerms := EvalTermsV
      |}
    .

    Class SyntacticMachines {ClosuresV EContextV clNegV clNegInjV EvalTermsV}
      := {
          asAM w: SClass (@asAbstractMachine w (ClosuresV w) (EContextV w) 
                                             (clNegV w) (clNegInjV w) (EvalTermsV w));
          ident w: (EContextV w).(Csupport) w;
          identP w: forall xp:w.(PLab), readp (ident w) xp = xp;
          identN w: forall xn:w.(NLab), readn (ident w) xn = inl xn
        }.

    Context `(SM:SyntacticMachines). 

    Variable WF: well_founded (relation (LAF:=LAF)).

    Variable TC: forall w0 w st (rho:(HeadRAlg (get (asAM w0)) WF).(SContexts) w) Gamma l (Delta:TypingDec st l) tl v, 
                   SemCont Gamma rho
                   -> SemTDec Delta (SemTermList (readE rho) tl) v
                   -> SemCont (Textends [Delta,tl] Gamma) (extends v rho).

    Theorem SHeadNormalisation:
        forall w Gamma (c : Command w), 
          CommandTyping Gamma c
          -> SN HeadReduction (SemC (M := HeadStruct (get (asAM w)))
                                   (ident w)
                                   c).
    Proof.
      move => w Gamma c H.      
      apply (HeadNormalisation (AM := get (asAM w))
                               (Gamma := Gamma)
                               (TC := @TC w)
            ) => //.
      rewrite /SemCont.
      simpl.
      split => //.
      split => [xp | xn] //.
      rewrite /Pard/getA/getTerms/ex2/ex1.
      elim (Treadn (t:=TContext) (w:=w) Gamma xn) => l [M tl].
      rewrite identN /SemNeg/ortho.
      elim => p v H0.
      simpl.
      apply toSN => x' H3.
      inversion H3.
      inversion H1.
    Qed.

  End SyntacticMachines.

End HeadReduction.

(* Print Assumptions HeadNormalisation. *)