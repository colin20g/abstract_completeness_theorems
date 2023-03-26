(** This text provides self contained formalized proofs of generalization of 
    the completeness theorem of propositional and first order predicate calculus. 
    It follows roughly 
    https://www.irif.fr/~krivine/articles/completude.pdf although
    for the first order part the generalization rule we use is slightly different but
    is the one that can be found in most presentations of proof theory based on Hilbert
    systems.   
    
    The most striking aspect (in the opinion of the author) of the completeness theorem 
    presented in the above article and here is the fact that the proof is intuitionistic 
    and that we can extract programs from it. No additional axioms were used in the 
    following coq file.
    
    The plan we follow differs from the article. All the sets of formulas involved are assumed 
    to be countable. 
    First we prove the Lindenbaum lemma (which is actually the propositional completeness 
    theorem) which asserts that for any formula F, 
    any set of formulas which doesn't proves F using classical propositional calculus is
    contained in a maximal consistent set formulas which doesn't either proves F with these 
    rules. When classical reasoning is available this theorem is obvious 
    (the set is built by induction). A slight modification of this argument gives
    the intuitionistic case.
    Then we prove the completeness theorem for predicate calculus by first order logic,
    by extending the theory adding Henkin constants and then exploiting the propositional case
    on the theory obtained.
    
    This method allows us to get models where witnesses are available for any universally
    quantified formula, which is a stronger form of the well known completeness theorem.
    Because of this, convenient applications are possible (e.g. easy proofs of skolemization).

 *)

Section General_type_tools.

  (** The sets of formulas that we'll consider further in the text are of
   the form "Formula -> Type" rather than "Formula -> Prop" in order to allow 
   full program extraction. The following tools are introduced in order to manipulate 
   these objects. *)
  
  Variable T:Type.

  Section Addition_of_a_new_item_to_a_type_valued_set.

    Variable P: T -> Type.
    Variable n:T.
    
    Inductive add_extra_item: T -> Type:=
    |aei_base: forall x:T, P x -> add_extra_item x
    |aei_new: add_extra_item n.
    
  End Addition_of_a_new_item_to_a_type_valued_set.

  Section Inclusion_of_type_valued_sets.

    Definition type_valued_inclusion (P Q: T -> Type):= forall x:T, P x -> Q x.

    Definition tvi_identity: forall P: T -> Type, type_valued_inclusion P P.
    Proof. unfold type_valued_inclusion; intros; assumption.
    Defined.

    Definition tvi_transitivity: forall A B C:T -> Type,
        type_valued_inclusion A B -> type_valued_inclusion B C -> type_valued_inclusion A C.
    Proof.
      unfold type_valued_inclusion. intros A B C i j x h; apply j; apply i; assumption.
    Defined.
    
  End Inclusion_of_type_valued_sets.

End General_type_tools.

Section A_classical_Hilbert_proof_system.

  Variable Sentence: Type.
  Variable s_implies: Sentence -> Sentence -> Sentence.

  Notation "a -o b":= (s_implies a b) (right associativity, at level 41).
  
  Section Definition_of_proofs.

    Variable Specific_axiom: Sentence -> Type.

    Inductive classical_propositional_implicative_theorem: Sentence -> Type:=
    |cpit_ax: forall x:Sentence, Specific_axiom x ->
                                 classical_propositional_implicative_theorem x
    |cpit_k: forall x y:Sentence, classical_propositional_implicative_theorem (x -o y -o x)
    |cpit_s: forall x y z:Sentence,
        classical_propositional_implicative_theorem ((x -o y -o z) -o (x -o y) -o x -o z)
    |cpit_Peirce: forall x y:Sentence,
        classical_propositional_implicative_theorem (((x -o y) -o x) -o x)
    |cpit_modus_ponens: forall x y:Sentence,
        classical_propositional_implicative_theorem (x -o y) ->
        classical_propositional_implicative_theorem x ->
        classical_propositional_implicative_theorem y.

    Definition cpit_i: forall x:Sentence, classical_propositional_implicative_theorem (x -o x).
    Proof.
      intros. apply cpit_modus_ponens with (x -o x -o x).
      apply cpit_modus_ponens with (x -o (x -o x) -o x). apply cpit_s. apply cpit_k.
      apply cpit_k.
    Defined.

    Definition cpit_syllogism: forall x y z:Sentence,
        classical_propositional_implicative_theorem (x -o y) ->
        classical_propositional_implicative_theorem (y -o z) ->
        classical_propositional_implicative_theorem (x -o z).
    Proof.
      intros. apply cpit_modus_ponens with (x:= x -o y).
      apply cpit_modus_ponens with (x:= x -o y -o z). apply cpit_s.
      apply cpit_modus_ponens with (x:= y -o z). apply cpit_k. assumption. assumption.
    Defined.
    
    Definition cpit_b: forall x y z:Sentence,
        classical_propositional_implicative_theorem ((y -o z) -o (x -o y) -o x -o z).
    Proof.
      intros. apply cpit_modus_ponens with (x:= (y -o z) -o x -o y -o z).
      apply cpit_modus_ponens with (x:= (y -o z) -o (x -o y -o z) -o (x -o y) -o x -o z).
      apply cpit_s. apply cpit_modus_ponens with (x:= (x -o y -o z) -o (x -o y) -o x -o z).
      apply cpit_k. apply cpit_s. apply cpit_k.
    Defined.
    
  End Definition_of_proofs.

  Definition cpit_subtheory: forall (A B: Sentence -> Type),
      type_valued_inclusion Sentence A B -> forall p:Sentence,
        classical_propositional_implicative_theorem A p ->
        classical_propositional_implicative_theorem B p.
  Proof.
    unfold type_valued_inclusion. intros A B i.
    apply classical_propositional_implicative_theorem_rect.
    intros; apply cpit_ax; apply i; assumption. apply cpit_k. apply cpit_s. apply cpit_Peirce.
    intros; apply cpit_modus_ponens with (x:=x); assumption.
  Defined.    
  
  Section The_deduction_theorem.

    Variable base_theory: Sentence -> Type.
    Variable new_sentence: Sentence.

    Definition cpit_deduction_theorem: forall (f: Sentence),
        classical_propositional_implicative_theorem
          (add_extra_item Sentence base_theory new_sentence) f ->
        classical_propositional_implicative_theorem base_theory (new_sentence -o f).
    Proof.
      apply classical_propositional_implicative_theorem_rect. intros. destruct s.
      apply cpit_modus_ponens with (x:= x). apply cpit_k. apply cpit_ax; assumption.
      apply cpit_i. intros; apply cpit_modus_ponens with (x:= x -o y -o x); apply cpit_k.
      intros; apply cpit_modus_ponens with (x:= (x -o y -o z) -o (x -o y) -o x -o z).
      apply cpit_k. apply cpit_s. 
      intros; apply cpit_modus_ponens with (x:= ((x -o y) -o x) -o x).
      apply cpit_k. apply cpit_Peirce. 
      intros. apply cpit_modus_ponens with (x:= new_sentence -o x). 
      apply cpit_modus_ponens with (x:= new_sentence -o x -o y). apply cpit_s.
      assumption. assumption.
    Defined.    
    
  End The_deduction_theorem.

  Definition cpit_triple_syllogism (theory: Sentence -> Type) (x a b c:Sentence):
    classical_propositional_implicative_theorem
      theory   
      ((a -o b -o c) -o (x -o a) -o (x -o b) -o (x -o c)).
  Proof.
    repeat apply cpit_deduction_theorem. apply cpit_modus_ponens with (x:= b).
    apply cpit_modus_ponens with (x:= a). apply cpit_ax.
    apply aei_base; apply aei_base; apply aei_base; apply aei_new.
    apply cpit_modus_ponens with (x:= x). apply cpit_ax.
    apply aei_base; apply aei_base; apply aei_new. apply cpit_ax; apply aei_new.
    apply cpit_modus_ponens with (x:= x). apply cpit_ax.
    apply aei_base; apply aei_new. apply cpit_ax; apply aei_new.
  Defined.    
  
  Section A_classical_tautology.

    Variable theory: Sentence -> Type.
    Variable a b c:Sentence.
    
    (** This theorem is not valid in intuitionistic logic*)

    Definition cpit_classical_cases_analysis:
      classical_propositional_implicative_theorem theory (a -o c) ->
      classical_propositional_implicative_theorem theory ((a -o b) -o c) ->
      classical_propositional_implicative_theorem theory c.
    Proof.
      intros p q. apply cpit_modus_ponens with (x := (c -o b) -o c). apply cpit_Peirce.
      apply cpit_deduction_theorem. apply cpit_modus_ponens with (x:= a -o b).
      apply cpit_subtheory with (A:= theory). intro; apply aei_base. assumption.
      apply cpit_syllogism with (y:= c). apply cpit_subtheory with (A:= theory).
      intro; apply aei_base. assumption. apply cpit_ax; apply aei_new.
    Defined.
    
  End A_classical_tautology.

  Section Propositional_Completeness.

    Variable indexation: nat -> Sentence.
    Variable countable: forall f:Sentence, {n:nat | indexation n = f}.
    
    Notation "T |- p" := (classical_propositional_implicative_theorem T p) (at level 42).
    Notation add_hypothesis := (add_extra_item Sentence).
    
    Section A_special_one_step_extension_of_a_theory.

      (** This paragraph is the only part where our text actually differs 
          from usual proofs of the Lindenbaum's lemma, in order to accomodate with 
          coq intuitionistic constraints. the rest of the text is tedious but 
       probably straightforward if the reader knows how to prove completeness
       according to the route we've chosen i.e. Lindenbaum -> propositional case -> 
       Henkin extension of a first order theory to exploit the propositional result. 
       All these further part are usually already constructive. *)
      
      Variable base_theory: Sentence -> Type.
      Variable addendum target: Sentence.

      Inductive inflate: Sentence -> Type:=
      |infl_base: forall x:Sentence, base_theory x -> inflate x
      |infl_new:
         ((add_hypothesis base_theory addendum |- target) -> base_theory |- target)
         -> inflate addendum.

      Lemma cpit_inflate_dichotomy: forall q:Sentence,
          inflate |- q ->
                     sum
                       ((add_hypothesis base_theory addendum |- target)
                        -> base_theory |- target)                      
                       (base_theory |- q).
      Proof.
        apply classical_propositional_implicative_theorem_rect. intros x i. destruct i.
        right; apply cpit_ax; assumption. left; assumption.
        intros; right; apply cpit_k. intros; right; apply cpit_s.
        intros; right; apply cpit_Peirce. intros x y ixy cxy ix cx. destruct cxy.
        left; assumption. destruct cx. left; assumption.
        right; apply cpit_modus_ponens with (x:=x); assumption.
      Defined.              
      
      Definition cpit_inflate_conservation:
        inflate |- target -> base_theory |- target.
      Proof.
        intro i. destruct (cpit_inflate_dichotomy target i) as [j|p]. apply j.
        apply cpit_subtheory with (A:= inflate). unfold type_valued_inclusion. intros x h.
        destruct h. apply aei_base; assumption. apply aei_new. assumption. assumption.
      Defined.        

      Definition cpit_inflate_already_proven_sentence:
        base_theory |- addendum -> inflate addendum.
      Proof.
        intro p. apply infl_new. intro q. apply cpit_deduction_theorem in q.
        apply cpit_modus_ponens with (x:= addendum); assumption.
      Defined.
      
    End A_special_one_step_extension_of_a_theory.

    Section The_Lindenbaum_maximal_construction.

      Variable ground_theory: Sentence -> Type.
      Variable target: Sentence.

      Fixpoint consistent_theory_sequence (n:nat) {struct n}: Sentence -> Type:=
        match n with
        | 0 => ground_theory
        | S m => inflate (consistent_theory_sequence m) (indexation m) target  
        end.

      Inductive Lindenbaum_maximal_theory: Sentence -> Type:=
      |lmt_intro: forall (k:nat) (f: Sentence),
          consistent_theory_sequence k f -> Lindenbaum_maximal_theory f.

      Fixpoint cts_conservation (n:nat) {struct n}:
        consistent_theory_sequence n |- target -> ground_theory |- target.
      Proof.
        destruct n. simpl; intro; assumption. simpl; intro p.
        apply cpit_inflate_conservation in p.  apply (cts_conservation n); assumption.
      Defined.

      Section Two_arithmetical_lemmas_about_the_max_of_integers.
        
        Lemma nat_max_symmetry: forall p q:nat, max p q = max q p.
        Proof.
          induction p. simpl. induction q. simpl; reflexivity. simpl; rewrite IHq; reflexivity.
          simpl. induction q. simpl; reflexivity. simpl. rewrite IHp; reflexivity.
        Defined.
        
        Lemma nat_max_succ: forall p q:nat,
            sum (max p (S q) = max p q) (max p (S q) = S (max p q)).
        Proof.
          induction p. simpl. intros; right; reflexivity. intros. simpl. 
          destruct q. left; rewrite nat_max_symmetry; simpl; reflexivity.
          destruct IHp with (q:=q). left; apply eq_S; assumption.
          right; apply eq_S; assumption.
        Defined.
        
      End Two_arithmetical_lemmas_about_the_max_of_integers.

      Definition cts_increasing:
        forall p q:nat, 
          type_valued_inclusion Sentence
                                (consistent_theory_sequence q)
                                (consistent_theory_sequence (max p q)).
      Proof.
        induction p. intros; apply tvi_identity. intros. rewrite nat_max_symmetry.
        destruct nat_max_succ with (p:=q) (q:=p). rewrite e. rewrite nat_max_symmetry.
        apply IHp. rewrite e. rewrite nat_max_symmetry.
        apply tvi_transitivity with (B:= consistent_theory_sequence (max p q)).
        apply IHp. simpl; intro; apply infl_base.
      Defined.

      Definition cpit_lmt_to_cts_index (f:Sentence) (pr: Lindenbaum_maximal_theory |- f):
        {n:nat & consistent_theory_sequence n |- f}.
      Proof.
        induction pr. destruct s as (k,q,r). exists k. apply cpit_ax; assumption.
        exists 0; apply cpit_k. exists 0; apply cpit_s. exists 0; apply cpit_Peirce.
        destruct IHpr1 as (p, prxy). destruct IHpr2 as (q, prx).
        exists (max p q). apply cpit_modus_ponens with (x:=x).
        apply cpit_subtheory with (A := consistent_theory_sequence p).
        rewrite nat_max_symmetry; apply cts_increasing. assumption.
        apply cpit_subtheory with (A := consistent_theory_sequence q).
        apply cts_increasing. assumption.
      Defined.

      Definition lmt_conservation:
        Lindenbaum_maximal_theory |- target -> ground_theory |- target.
      Proof.
        intros p. destruct (cpit_lmt_to_cts_index target p) as (k,q).
        apply cts_conservation with (n:= k); assumption.
      Defined.

      Definition lmt_counter_model:
        Lindenbaum_maximal_theory target -> ground_theory |- target.
      Proof.
        intros; apply lmt_conservation. apply cpit_ax; assumption.
      Defined.

      Definition lmt_belonging_criterion (x:Sentence):
        (Lindenbaum_maximal_theory |- x -o target -> Lindenbaum_maximal_theory |- target) ->
        Lindenbaum_maximal_theory x.
      Proof.
        intros. destruct countable with (f:=x) as (m, e). apply lmt_intro with (k := S m).
        simpl. rewrite e. apply infl_new. intro a. apply cpit_deduction_theorem in a.
        apply cpit_subtheory with (A:= ground_theory). assert (m = max m 0) as E. 
        rewrite nat_max_symmetry. simpl; reflexivity. rewrite E.
        apply cts_increasing with (p:= m) (q:= 0). apply lmt_conservation. apply X.
        apply cpit_subtheory with (A:= consistent_theory_sequence m).
        intro; apply lmt_intro. assumption.
      Defined.

      Definition lmt_modus_ponens_stability: forall x y:Sentence,
          Lindenbaum_maximal_theory (x -o y) ->
          Lindenbaum_maximal_theory x ->
          Lindenbaum_maximal_theory y.
      Proof.
        intros. apply lmt_belonging_criterion. intros. apply cpit_modus_ponens with (x:= x).
        apply cpit_syllogism with (y := y). apply cpit_ax; assumption. assumption.
        apply cpit_ax; assumption.
      Defined.              

      Definition lmt_reverse_modus_ponens: forall x y:Sentence,
          (Lindenbaum_maximal_theory x -> Lindenbaum_maximal_theory y) ->
          Lindenbaum_maximal_theory (x -o y).
      Proof.
        intros x y h. apply lmt_belonging_criterion. intro k.
        apply cpit_classical_cases_analysis with (a:= x) (b:= y).
        apply cpit_deduction_theorem. apply cpit_modus_ponens with (x:= y).
        apply cpit_subtheory with (A:= Lindenbaum_maximal_theory). intro; apply aei_base.
        apply cpit_syllogism with (y := x -o y). apply cpit_k. assumption.
        apply cpit_subtheory with (A:= Lindenbaum_maximal_theory). intro; apply aei_base.
        apply cpit_ax. apply h. apply lmt_belonging_criterion. intro l.
        apply cpit_classical_cases_analysis with (a:= x) (b:= y); assumption. assumption.
      Defined.

      Definition lmt_proof_stability (f:Sentence) (pr: Lindenbaum_maximal_theory |- f):
        Lindenbaum_maximal_theory f.
      Proof.
        induction pr. assumption.
        destruct countable with (f:= x -o y -o x) as (m,e).
        apply lmt_intro with (k:=(S m)). simpl. rewrite e.
        apply cpit_inflate_already_proven_sentence. apply cpit_k.
        destruct countable with (f:= (x -o y -o z) -o (x -o y) -o x -o z) as (m,e).
        apply lmt_intro with (k:=(S m)). simpl. rewrite e.
        apply cpit_inflate_already_proven_sentence. apply cpit_s.
        destruct countable with (f:= ((x -o y) -o x) -o x) as (m,e).
        apply lmt_intro with (k:=(S m)). simpl. rewrite e.
        apply cpit_inflate_already_proven_sentence. apply cpit_Peirce.
        apply lmt_modus_ponens_stability with (x:= x); assumption.
      Defined.
      
    End The_Lindenbaum_maximal_construction.

    Section Concise_reformulation_of_results.

      Variable theory: Sentence -> Type.

      Definition classical_propositional_model (M: Sentence -> Type):=
        prod (type_valued_inclusion Sentence theory M)
             (prod (forall x y:Sentence, M (((x -o y) -o x) -o x))
                   (forall x y:Sentence,
                       prod (M (x -o y) -> M x -> M y)
                            ((M x -> M y) -> M (x -o y))
                   )
             ).

      Definition classical_propositional_soundness_theorem:
        forall (M: Sentence -> Type) (f: Sentence),
          classical_propositional_model M ->
          theory |- f -> M f.
      Proof.
        intros M f m p. unfold classical_propositional_model in m. destruct m as (a,(b,c)).
        induction p. apply a; assumption. apply c with (x:= x) (y:= y -o x).
        intro u. apply c. intro v; assumption.
        apply c; intro u; apply c; intro v; apply c; intro w.
        apply c with (x := y). apply c with (x := x). assumption. assumption.
        apply c with (x := x); assumption. apply b. apply c with (x := x); assumption.
      Defined.

      Definition constructive_classical_propositional_completeness_theorem:
        forall h:Sentence,
          {M: Sentence -> Type & prod (classical_propositional_model M)
                                      (M h -> theory |- h)}.
      Proof.
        intros. exists (Lindenbaum_maximal_theory theory h). split.
        unfold classical_propositional_model. split. intro; apply lmt_intro with (k := 0).
        split. intros; apply lmt_proof_stability; apply cpit_Peirce. intros. split.
        intros. apply lmt_modus_ponens_stability with (x:= x); assumption.
        apply lmt_reverse_modus_ponens. apply lmt_counter_model.
      Defined.

      Definition classical_propositional_completeness_theorem:
        forall h:Sentence,
          prod (theory |- h ->
                          forall M:Sentence -> Type, classical_propositional_model M -> M h)
               ((forall M:Sentence -> Type, classical_propositional_model M -> M h) ->
                theory |- h).
      Proof.
        intros; split. intros; apply classical_propositional_soundness_theorem; assumption.
        intros R; destruct constructive_classical_propositional_completeness_theorem
                    with (h:= h) as (N,q). apply q; apply R; apply q.
      Defined.
      
    End Concise_reformulation_of_results.

  End Propositional_Completeness.

End A_classical_Hilbert_proof_system.

Section Abstract_classical_first_order_systems.

  Variable General_Property: Type.
  Variable Term:Type.
  Variable gp_implies: General_Property -> General_Property -> General_Property.
  Variable gp_specialize: General_Property -> Term -> General_Property.
  Variable gp_fresh_variable: General_Property -> General_Property -> Term.
  Variable gp_theorem: General_Property -> Type.
  
  Notation "a -o b" := (gp_implies a b) (right associativity, at level 41).
  Notation "|- a" := (gp_theorem a) (at level 44).

  Variable gp_k: forall x y:General_Property, |- x -o y -o x.
  Variable gp_s: forall x y z:General_Property, |- (x -o y -o z) -o (x -o y) -o x -o z.
  Variable gp_Peirce: forall x y: General_Property, |- ((x -o y) -o x) -o x.
  Variable gp_special_case: forall (f:General_Property) (t:Term), |- f -o (gp_specialize f t).
  Variable gp_modus_ponens: forall x y:General_Property, |- x -o y -> |- x -> |- y.
  Variable gp_generalization_rule: forall p q:General_Property,
      |- p -o gp_specialize q (gp_fresh_variable p q) ->
      |- p -o q.

  (** We explain what the objects above and especially "gp_specialize" and "gp_fresh_variable"
      maps are intended to mean.
      A "general property" is simply a first order formula over a given signature.
      Let f be such a formula and t a term of the language. if f is "forall x, g" where
      g is another formula, then "gp_specialize f t" is nothing but g<x := t>, i.e.
      the the result of the capture-free substitution of x by t in g. In every other cases,
      gp_specialize f t is f itself. This justifies the name "General_Property" we've picked.
      If n -> v_n is the sequence of all the variables of the language (which will be 
      assumed to be countable in the further developments), then for every formulas a,b,  
      "gp_fresh_variable a b" is v_m where m is the smallest integer such that v_m has
      no free occurences in a or in b (if you don't know what that means: take "v_m doesn't
      appears in a or in b", this would give the same results at the end).
      gp_theorem is the proof system used and the properties "gp_special_case" and 
      "gp_generalization_rule" are obvious (wether f and p are of the form 
      "forall x g" or not). The program offered is general enough so that hopefully it can 
      be used in any reasonable implementation of first order logic. The only real constraint 
      is that the set of formulas is countable.
      
      No soundness theorem is provided (such a result would depend on how gp_theorem is 
      actually defined), the user will have to provide one (which is usually easy).
   *)
  
  Section Basic_proof_theoretic_results.

    Ltac mp t := apply gp_modus_ponens with (x:= t).
    
    Section propositional_proof_to_gp_theorem.

      Variable T: General_Property -> Type.
      Variable t_incl: type_valued_inclusion General_Property T gp_theorem.

      Definition cpit_inclusion_to_gp: forall p:General_Property,
          classical_propositional_implicative_theorem General_Property gp_implies T p -> |- p.
      Proof.
        apply classical_propositional_implicative_theorem_rect.
        intros; apply t_incl; assumption. apply gp_k. apply gp_s. apply gp_Peirce.
        intros; mp x; assumption.
      Defined.               
      
    End propositional_proof_to_gp_theorem.

    Definition cpit_to_gp: forall p:General_Property,
        classical_propositional_implicative_theorem General_Property gp_implies gp_theorem p
        -> |- p:= cpit_inclusion_to_gp gp_theorem (tvi_identity General_Property gp_theorem). 

    Definition gp_syllogism (x y z:General_Property): |- x -o y -> |- y -o z -> |- x -o z.
    Proof.
      intros. mp (x -o y). mp (x -o y -o z). apply gp_s. mp (y -o z). apply gp_k. assumption.
      assumption.
    Defined.

    Ltac syl t := apply gp_syllogism with (y:= t).
    
    Definition gp_permutation_insertion: forall x y z:General_Property,
        |- x -o y -o z -> |- y -> |- x -o z.
    Proof.
      intros. mp (x -o y). mp (x -o y -o z). apply gp_s. assumption. mp y. apply gp_k.
      assumption.
    Defined.

    Definition gp_universal_witness_property: forall g h:General_Property,
        |- (gp_specialize g (gp_fresh_variable (h -o g) g) -o g) -o h -> |- h.
    Proof.
      intros. mp ((h -o g) -o h). apply gp_Peirce. syl g. apply gp_generalization_rule.
      syl ((gp_specialize g (gp_fresh_variable (h -o g) g) -o g)
           -o gp_specialize g (gp_fresh_variable (h -o g) g)).
      syl ((gp_specialize g (gp_fresh_variable (h -o g) g) -o g) -o g).
      apply gp_permutation_insertion with
          (y:= (gp_specialize g (gp_fresh_variable (h -o g) g) -o g) -o h).
      apply cpit_to_gp; apply cpit_b. assumption.
      mp (g -o gp_specialize g (gp_fresh_variable (h -o g) g)). 
      apply cpit_to_gp; apply cpit_b. apply gp_special_case. apply gp_Peirce.
      syl (gp_specialize g (gp_fresh_variable (h -o g) g) -o g). apply gp_k. assumption.
    Defined.
    
  End Basic_proof_theoretic_results.

  Section Abstract_first_order_completeness.

    Variable indexation: nat -> General_Property.
    Variable countable: forall f:General_Property, {n:nat | indexation n = f}.
    Variable target: General_Property.

    Section The_associated_Henkin_extension_of_a_theory.

      Fixpoint gp_Henkin_auxiliary_formula (n:nat) {struct n}: General_Property:=
        match n with
        | 0 => target
        | S m =>
          (gp_specialize (indexation m)
                         (gp_fresh_variable
                            ((gp_Henkin_auxiliary_formula m) -o indexation m)
                            (indexation m)) -o (indexation m)
          )
          -o gp_Henkin_auxiliary_formula m 
        end.
      
      Notation gp_Henkin_universal_constant :=
        (fun (k:nat) =>
           gp_fresh_variable
             ((gp_Henkin_auxiliary_formula k) -o indexation k) (indexation k)).

      Definition gp_universal_witness (f: General_Property): Term:=
        gp_Henkin_universal_constant (proj1_sig (countable f)).
      
      Notation critical_formula:=
        (fun n:nat => (gp_specialize (indexation n) (gp_Henkin_universal_constant n))
                      -o indexation n).
      
      Inductive gp_Henkin_theory: General_Property -> Type:=
      |gpht_base: forall x:General_Property, gp_theorem x -> gp_Henkin_theory x
      |gpht_critical_formula: forall n:nat,
          gp_Henkin_theory (critical_formula n).              

      Definition gpuw_critical_belongs_to_Henkin: forall (f: General_Property),
          gp_Henkin_theory ((gp_specialize f (gp_universal_witness f)) -o f).
      Proof.
        intros. unfold gp_universal_witness. destruct (countable f). simpl. rewrite <- e.
        apply gpht_critical_formula.
      Defined.          
      
      Fixpoint gp_add_to_tail (head: General_Property) (n:nat) {struct n}:General_Property:=
        match n with
        | 0 => head
        | S m => (critical_formula m) -o (gp_add_to_tail head m) 
        end.

      Fixpoint gp_att_k (x:General_Property) (n:nat) {struct n}:
        gp_theorem (x -o (gp_add_to_tail x n)).
      Proof.
        destruct n. simpl. apply cpit_to_gp; apply cpit_i. simpl.
        apply gp_syllogism with  (y:= gp_add_to_tail x n). apply gp_att_k. apply gp_k.
      Defined.

      Definition nat_max_sum (p:nat): forall q:nat, (p - q) + q = max p q.
      Proof.
        induction p. simpl; intros; reflexivity. intros; simpl.
        destruct q. apply eq_sym;  apply plus_n_O. rewrite <- plus_n_Sm. apply eq_S.
        apply IHp.
      Defined.

      Definition gp_att_max: forall (x:General_Property) (p q:nat),
          gp_theorem (gp_add_to_tail x p) -> gp_theorem (gp_add_to_tail x (max q p)).
      Proof.
        intros. rewrite <- nat_max_sum.
        assert (forall d:nat, gp_theorem (gp_add_to_tail x (d + p))) as LEMMA.
        induction d. simpl; assumption.
        apply gp_modus_ponens with (x := gp_add_to_tail x (d + p)). simpl; apply gp_k.
        assumption. apply LEMMA.
      Defined.

      Definition gp_att_modus_ponens: forall (n:nat) (x y:General_Property),
          |- gp_add_to_tail (x -o y) n ->
          |- gp_add_to_tail x n ->
          |- gp_add_to_tail y n.
      Proof.
        assert (forall (x y:General_Property) (n:nat),
                   |- (gp_add_to_tail (x -o y) n)
                      -o (gp_add_to_tail x n) -o (gp_add_to_tail y n)) as LEMMA.
        intros x y. induction n. simpl; apply cpit_to_gp; apply cpit_i.
        apply gp_modus_ponens with
            (x := gp_add_to_tail (x -o y) n
                  -o (gp_add_to_tail x n) -o (gp_add_to_tail y n)).
        apply cpit_to_gp. simpl; apply cpit_triple_syllogism. assumption.
        intros. apply gp_modus_ponens with (x := gp_add_to_tail x n).
        apply gp_modus_ponens with (x := gp_add_to_tail (x -o y) n). apply LEMMA.
        assumption. assumption.
      Defined.
      
      Lemma gp_att_proof: forall (f: General_Property),
          classical_propositional_implicative_theorem
            General_Property gp_implies (gp_Henkin_theory) f ->
          {n: nat & |- gp_add_to_tail f n}.
      Proof.
        apply classical_propositional_implicative_theorem_rect.
        intros. destruct s. exists 0; assumption. exists (S n). simpl; apply gp_att_k.
        intros; exists 0; simpl; apply gp_k.
        intros; exists 0; simpl; apply gp_s.
        intros; exists 0; simpl; apply gp_Peirce.
        intros x y txy cxy tx cx. destruct cxy as (p, pxy). destruct cx as (q, px).
        apply gp_att_max with (q:= q) in pxy. apply gp_att_max with (q:= p) in px.
        rewrite nat_max_symmetry in pxy. exists (max p q).
        apply gp_att_modus_ponens with (x:= x); assumption.
      Defined.          

      Definition gp_Henkin_auxiliary_formula_elimination: forall n:nat,
          |- gp_Henkin_auxiliary_formula n -> |- target.
      Proof.
        induction n. simpl; intro; assumption.
        simpl; intro C; apply gp_universal_witness_property in C; apply IHn; assumption.
      Defined.

      Definition gp_att_haf_equality: forall n:nat,
          gp_add_to_tail target n = gp_Henkin_auxiliary_formula n.
      Proof.
        induction n. simpl; reflexivity. simpl; rewrite IHn; reflexivity.
      Defined.
      
      Definition gp_Henkin_theory_conservation:
        classical_propositional_implicative_theorem
          General_Property gp_implies (gp_Henkin_theory) target ->
      |- target.
      Proof.
        intro pr. apply gp_att_proof in pr. destruct pr as (m,t).
        rewrite gp_att_haf_equality in t. apply (gp_Henkin_auxiliary_formula_elimination m).
        assumption.
      Defined.          
      
    End The_associated_Henkin_extension_of_a_theory.    

    Definition abstract_first_order_model (M: General_Property -> Type):=
      prod (type_valued_inclusion General_Property gp_theorem M)
           (prod (forall x y:General_Property, M (((x -o y) -o x) -o x))
                 (prod (forall x y:General_Property,
                           prod (M (x -o y) -> M x -> M y)
                                ((M x -> M y) -> M (x -o y)))
                       (forall f:General_Property,
                           prod
                             (M f -> forall t:Term, M (gp_specialize f t))
                             ((forall t:Term, M (gp_specialize f t)) -> M f)
                             
                       )
           )).

    (** The following maps build the "drinker" in the "drinker's paradox", 
     when f means "everyone drinks". if g is any first order formula, 
     a witnessing function w, when applied to some "forall x, g", will reliably provide a 
     counterexample for g whenever there is one i.e. forall x, g is not true.
     *)
    
    Definition abstract_first_order_witnessing_function
               (M: General_Property -> Type) (w: General_Property -> Term):=
      forall f: General_Property, M (gp_specialize f (w f) -o f).

    (** Not only we construct a model, but one where there is a witnessing function *)
    Definition constructive_abstract_first_order_completeness_theorem_with_witnessing_function:
      {M: General_Property
          -> Type
             &
             {f: General_Property
                 -> Term
                    &
                    prod
                      (abstract_first_order_model M )
                      (prod (abstract_first_order_witnessing_function M f)
                            (M target -> |- target))
      }}.
    Proof.
      destruct
        (constructive_classical_propositional_completeness_theorem
           General_Property
           gp_implies
           indexation
           countable
           gp_Henkin_theory
           target
        )
        as (M,p).
      exists M. exists gp_universal_witness. unfold abstract_first_order_model.
      unfold classical_propositional_model in p. destruct p as ((i,q),r).
      assert (forall g:General_Property,
                 M (gp_specialize g (gp_universal_witness g) -o g)) as W. intros. apply i.
      apply gpuw_critical_belongs_to_Henkin. split. split.
      apply tvi_transitivity with (B:= gp_Henkin_theory). intro; apply gpht_base. apply i.
      split. apply q. split. apply q. intro f; split. intros.
      apply q with (x:= f) (y:= gp_specialize f t).
      apply i; apply gpht_base; apply gp_special_case. assumption.
      intros l. apply q with (x:= gp_specialize f (gp_universal_witness f)). apply W. apply l.
      split. unfold abstract_first_order_witnessing_function. apply W. intro k.
      apply r in k. apply gp_Henkin_theory_conservation in k. assumption.
    Defined.     

    Definition abstract_first_order_completeness_theorem_with_witnessing_function:
      (forall (M: General_Property -> Type) (w: General_Property -> Term),
        abstract_first_order_model M -> abstract_first_order_witnessing_function M w -> 
        M target) -> |- target.
    Proof.
      intros a.
      destruct 
        constructive_abstract_first_order_completeness_theorem_with_witnessing_function
        as (M,(w,p)). apply p. apply a with (w := w). apply p. apply p.
    Defined.
    
  End Abstract_first_order_completeness.
  
End Abstract_classical_first_order_systems.
