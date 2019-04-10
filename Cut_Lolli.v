(* Project files imports *)
Require Import MyLists.
Require Import Sequent_Calculus.
Require Import Basic_Properties.

(* Other imports *)
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
Import Wf_nat.



Theorem cut_lolli :
  forall (A B : formula),
    (forall (n m : nat) (C : formula)
            (Gamma Delta1 Delta2 : list formula),
        (n; Gamma |- A) ->
        (m; Delta1 ++ [A] ++ Delta2 |- C) ->
        exists z : nat,
          (z; Gamma ++ Delta1 ++ Delta2 |- C))
    ->
    (forall (n m : nat) (C : formula)
            (Gamma Delta1 Delta2 : list formula),
        (n; Gamma |- B) ->
        (m; Delta1 ++ [B] ++ Delta2 |- C) ->
        exists z : nat,
          (z; Gamma ++ Delta1 ++ Delta2 |- C))
    ->
    forall (n m : nat)
           (C: formula)
           (Gamma Delta1 Delta2 : list formula),
      (n; Gamma |- (A -o B))
      ->
      (m; Delta1 ++ [A -o B] ++ Delta2 |- C)
      -> exists z, z; (Gamma ++ Delta1 ++ Delta2) |- C.
Proof.
  intros A B IHA1 IHA2 n m.
  (* We start induction on depth of proof *)
  (* This is necessary for Commuting Conversions *) 
  remember (n + m) as l.
  generalize dependent m.
  generalize dependent n.
  induction (lt_wf l) as [l _ IHl].
  
  intros n m sum C Gamma Delta1 Delta2 LH.
  remember (A -o B) as cutF.

  (* By cases on LH *)
  destruct LH.

  (* LH = OneL *)
  * intros RH.
    subst. clear IHA1. clear IHA2. 
    
    assert (eq1: n + m < S n + m) by omega.
    assert (eq2: n + m = n + m) by omega.
    specialize (IHl (n + m) eq1 n m eq2
                    C Gamma Delta1 Delta2 LH RH).
    clear eq1. clear eq2. clear RH. clear LH.
    
    destruct IHl as [z Hyp].
    exists (S z).
    simpl in *.
    constructor; auto.
    
  (* LH = OneR *)
  * discriminate.

  (* LH = Axiom *)
  * intros RH.
    subst. clear IHA1. clear IHA2. 
    assert (RH' : m; [] ++ Delta1 ++ [A -o B]
                       ++ Delta2 |- C)
      by auto.
    apply exchange_with_env_l in RH'.
    exists (m + length Delta1).
    assumption.

  (* LH = TensorL *)
  * intros RH.
    subst. clear IHA1. clear IHA2.

    assert (eq1: n + m < S n + m) by omega.
    assert (eq2: n + m = n + m) by omega.
    specialize (IHl (n + m) eq1 n m eq2
                    C (A0::B0::env)
                    Delta1 Delta2 LH RH).
    clear eq1. clear eq2. clear RH. clear LH.
    
    destruct IHl as [z Hyp].
    exists (S z).
    simpl in *.
    constructor; auto.

    (* LH = TensorR *)
  * discriminate. 
      
  (* LH is LolliL *)
  * intros RH.
    subst. clear IHA1. clear IHA2.
      
    assert (eq1: n + m < S n + m) by omega.
    assert (eq2: n + m = n + m) by omega.
    specialize (IHl (n + m) eq1
                    n m  eq2
                    C
                    (B0 :: env2)
                    Delta1 Delta2 LH2 RH
               ).
    clear eq1. clear eq2. clear RH. clear LH2.
    destruct IHl as [z IHl].

    assert (z; B0:: env2 ++ Delta1
                 ++ Delta2 |- C) by auto.
    apply (level_depth
             n env1 A0
             z (B0::env2 ++ Delta1 ++ Delta2) C
             LH1) in H.
    clear LH1. destruct H as [k [H1 H2]].

    apply (LolliL k env1 A0
                   (env2 ++ Delta1 ++ Delta2) B0 C
                   H1) in H2.

    exists (S k).
    assert (eq: S k;
            ([A0 -o B0] ++ env1 ++ env2)
              ++ Delta1 ++ Delta2  |- C)
      by (repeat rewrite <- app_assoc in *; auto).
    auto.
    
  (* LH is LolliR *)
  * intros RH.
    subst.
    remember (Delta1 ++ [A0 -o B0] ++ Delta2) as CF. 
    inversion HeqCF as [backup].
    assert(Premise: n; A0 :: env |- B0) by auto.
    apply (LolliR n env A0 B0) in LH.

    {
      destruct RH.

      (* RH is OneL *)
      - apply element_in_app_head in HeqCF.

        destruct HeqCF as [Left | Right].

        * destruct Left as [t1 [t2 t3]].
          discriminate.

        * destruct Right as [l H].
          inversion HeqcutF. 
          subst.
          clear HeqcutF. clear IHA1. clear IHA2.
          assert (eq: (One :: l) ++ [A -o B] ++ Delta2 =
                      Delta1 ++ A -o B :: Delta2)
            by auto.
          apply app_inv_tail in eq.
          subst. clear backup.
          
          assert (eq1: S n + n0 < S n + S n0) by omega.
          assert (eq2: S n + n0 = S n + n0) by omega.
          specialize (IHl (S n + n0) eq1 (S n) n0 eq2
                    A1 env l Delta2 LH RH).
          clear eq1. clear eq2. clear RH. clear LH.

          destruct IHl as [z H].
          apply OneL in H.
          assert (eq: S z; [] ++ [One] ++ env ++ l
                              ++ Delta2 |- A1)
            by auto.
          apply exchange_with_env_r in eq.
          assert (Hyp:
                    (S z + length env);
                  env ++ ([One] ++ l)
                      ++ Delta2 |- A1) by auto.
          
          exists (S z + length env); auto.
          
      (* RH is OneR *)
      - simpl in *.
        apply app_cons_not_nil in HeqCF.
        destruct HeqCF. 

      (* RH is Atom *)
      - inversion HeqcutF.
        subst. clear HeqcutF. clear IHA1. clear IHA2.
        apply element_in_app_head in HeqCF.

        destruct HeqCF as [Left | Right].

        * destruct Left as [t1 [t2 t3]].
          subst.
          exists (S n).
          rewrite app_nil_r; auto.

        * destruct Right as [l H].
          apply app_cons_not_nil in H.
          destruct H. 

      (* RH is TensorL *)
      - apply element_in_app_head in HeqCF.

        destruct HeqCF as [Left | Right].

        * destruct Left as [t1 [t2 t3]].
          discriminate.

        * destruct Right as [l H].
          subst.
          assert (eq: (A1 ** B1 :: l)
                        ++ [A0 -o B0] ++ Delta2 =
                      Delta1 ++ [A0 -o B0] ++ Delta2)
            by auto.
          apply app_inv_tail in eq.
          inversion HeqcutF. 
          subst. clear backup.
          
          assert (eq1: S n + n0 < S n + S n0) by omega.
          assert (eq2: S n + n0 = S n + n0) by omega.
          specialize (IHl (S n + n0) eq1 (S n) n0 eq2
                          C env
                          (A1::B1::l)
                          Delta2 LH RH).
          clear eq1. clear eq2. clear RH. clear LH.

          destruct IHl as [z H].

          rewrite app_assoc in H.
          apply exchange_subset in H.
          destruct H as [m [ _ H]].

          assert( eq: m;
                  [A1] ++ [B1]
                       ++ l ++ env ++ Delta2 |- C)
            by (repeat rewrite <- app_assoc in *; auto).
          simpl in eq.

          apply (TensorL m (l ++ env ++ Delta2) A1 B1 C)
            in eq.

          assert (eq': S m;
                  ((A1 ** B1 :: l) ++ env)
                    ++ Delta2 |- C)
            by (repeat rewrite <- app_assoc in *; auto).

          apply exchange_subset in eq'.
          destruct eq' as [k [ _ Final]].
          rewrite <- app_assoc in Final.

          exists k; auto.          

      (* RH is TensorR *)
      - (* cleaning *)
        clear IHA1. clear IHA2.
        inversion HeqcutF.
        subst. clear HeqcutF.

        (* some pre-processing of IHl *)
        assert (eq1: S n + n0 < S n + S n0) by omega. 
        assert (eq2: S n + n0 = S n + n0) by omega.    
        specialize (IHl (S n + n0) eq1 (S n) n0 eq2).
        clear eq1. clear eq2.

        (* We go by cases, since A1 -o A2 could be in RH1 or RH2 *)
        apply element_in_app in HeqCF.
        {
          destruct HeqCF as [inEnv1 | inEnv2].

          (* on the left *)
          - destruct inEnv1 as [t1 [t2 [l t3]]].
            subst. clear t1. clear t2.

            (* one more infere&substitute *)
            assert (eq: (Delta1 ++ [A -o B]) ++ (l ++ env2) =
                        (Delta1 ++ [A -o B]) ++ Delta2).
            { repeat rewrite <- app_assoc in *. auto. }
            apply app_inv_head in eq. subst. clear backup.
            
            specialize (IHl A1 env Delta1 l LH RH1).
            clear LH. clear RH1.
            destruct IHl as [z LH].

            apply (level_depth z (env ++ Delta1 ++ l) A1
                               n0 env2 B1 LH) in RH2.
            clear LH.
            destruct RH2 as [k [LH RH]].
                               
            exists (S k).
            rewrite app_assoc.
            rewrite app_assoc.
            constructor; [rewrite <- app_assoc; auto | auto].
            
          (* on the right *)
          - destruct inEnv2 as [t1 [t2 [l t3]]].
            subst. clear t1. clear t2.

            (* one more infere&substitute *)
            assert (eq: (env1 ++ l) ++ ([A -o B] ++ Delta2) =
                        Delta1 ++ (A -o B :: Delta2))
              by (repeat rewrite <- app_assoc in *; auto). 
            apply app_inv_tail in eq. subst.
            clear backup.
            
            specialize (IHl B1 env l Delta2 LH RH2).
            clear LH. clear RH2.
            destruct IHl as [z LH].

            apply (level_depth z (env ++ l ++ Delta2) B1
                               n0 env1 A1 LH) in RH1.
            clear LH.
            destruct RH1 as [k [RH LH]].

            pose proof (TensorR k env1 A1 (env ++ l ++ Delta2) B1
                                LH RH).
            assert (eq: S k; (env1 ++ env) ++ l ++ Delta2
                           |- (A1 ** B1))
              by (rewrite <- app_assoc; auto ).
            apply exchange_subset in eq.
            destruct eq as [m [temp final]]. clear temp.
            exists m.
            repeat rewrite <- app_assoc in *; auto.
        }

        (* RH is LolliL *)
      - inversion HeqcutF.
        subst. 
        (* we need to proceed by cases *)
        assert (eq: (A1 -o B1 :: env1) ++ env2 =
                    Delta1 ++ [A -o B] ++ Delta2) by auto.
        apply element_in_app in eq.
        {
          destruct eq as [inLeft | inRight].
          
          (* on the left *)
          - destruct inLeft as [t1 [t2 [l t3]]]. clear t1. clear t2.

            (* we have two more cases: reduce or commute *)
            assert (eq: [A1 -o B1] ++ env1 =
                        Delta1 ++ [A -o B] ++ l) by auto.
            apply element_in_app in eq.

            {
              destruct eq as [reduction | commute].

              (* reduction case *)
              - destruct reduction as [_ [_ [l' t]]].
              apply app_singleton in t.
              destruct t as [t1 [t2 t4]].
              inversion t4.
              subst. clear t4. 
              inversion t3.
              subst.
              inversion backup.
              subst. clear backup. clear HeqCF. 
              clear HeqcutF. clear LH.
              clear t3. clear IHl. 

              assert (LH: n; [] ++ A :: env |- B) by auto.
              apply (IHA1 n0 n B l [] env RH1) in LH.
              destruct LH as [z LH].
              simpl in LH.
              
              assert (RH: n0; [] ++ B :: env2 |- C) by auto.
              apply (IHA2 z n0 C (l ++ env)
                          [] env2 LH) in RH.
              destruct RH as [z' H].
              simpl in *.
              apply exchange_subset in H.
              destruct H as [m [ _ H]].
              rewrite app_assoc.
              exists m; auto.

               
              (* commute case *)
              - destruct commute as [t1 [t2 [l' t4]]].
                clear t1. clear t2. clear IHA1. clear IHA2.
                
                (* some substitutions *)
                subst.
                assert (eq: (A1 -o B1 :: l') ++ ([A -o B] ++ l) =
                            Delta1 ++ ([A -o B] ++ l)) by auto.
                apply app_inv_tail in eq.
                subst. clear t3. 
                assert (eq: ([A1 -o B1] ++ l' ++ [A -o B]) ++ l ++
                                 env2 =
                            ([A1 -o B1] ++ l' ++ [A -o B])
                              ++ Delta2).
                { repeat rewrite <- app_assoc in *. auto. }
                apply app_inv_head in eq.
                subst.
                clear backup. clear Premise. clear HeqCF.
                
                assert (eq1: S n + n0 < S n + S n0) by omega. 
                assert (eq2: S n + n0 = S n + n0) by omega.
                specialize (IHl (S n + n0) eq1
                                (S n) n0 eq2
                                A1 env l' l LH RH1).
                clear eq1. clear eq2. clear LH. clear RH1.
                destruct IHl as [z Last].

                apply (level_depth z (env ++ l' ++ l) A1
                                   n0 (B1::env2) C Last) in RH2.

                destruct RH2 as [k [First Second]].
                pose proof (LolliL k (env ++ l' ++ l)
                                   A1
                                   env2 B1 C First Second).

                assert(eq: S k; [] ++ [A1 -o B1] ++ env
                                   ++ l' ++ l ++ env2 |- C).
                { simpl in *. repeat rewrite <- app_assoc in *.
                  auto. }

                apply exchange_with_env_r in eq.

                exists (S k + length env); auto.
            }

          (* on the right *)
          - destruct inRight as [t1 [t2 [l t3]]].
            clear t1. clear t2. clear IHA1. clear IHA2.

            (* first some subst, to simplify *)
            subst.
            assert (eq: (A1 -o B1 :: env1 ++ l) ++
                                              (A -o B :: Delta2)
                        =
                        Delta1 ++ (A -o B :: Delta2)).
            { simpl in *.
              repeat rewrite <- app_assoc in *. auto. }
            apply app_inv_tail in eq.
            subst.
            clear backup. clear HeqCF. clear HeqcutF.

            assert (eq1: S n + n0 < S n + S n0) by omega. 
            assert (eq2: S n + n0 = S n + n0) by omega.
            specialize (IHl (S n + n0) eq1
                            (S n) n0 eq2
                            C env (B1::l) Delta2 LH RH2).
            clear eq1. clear eq2. clear LH. clear RH2.
            destruct IHl as [z Last].

            assert (eq1: z; [] ++ env ++ [B1] ++ l ++ Delta2 |- C)
              by auto.

            apply exchange_with_env_l in eq1.
            simpl in eq1. 
            apply (level_depth
                     (z + length env) (B1 :: env ++ l ++ Delta2) C
                     n0 env1 A1 eq1) in RH1.
            clear eq1. clear Last.
            
            destruct RH1 as [k [RH LH]].

            pose proof (LolliL k env1 A1
                               (env ++ l ++ Delta2) B1 C
                               LH RH).

            assert (eq1: S k; (([A1 -o B1] ++ env1)
                                 ++ env) ++ l ++ Delta2
                              |- C).
            { repeat rewrite <- app_assoc in *.
              simpl. auto. }

            apply exchange_subset in eq1.
            destruct eq1 as [m [temp Final]].

            exists m.

            assert (eq1:  m; env ++ ([A1 -o B1] ++ env1 ++ l)
                                 ++ Delta2 |- C).
            { repeat rewrite <- app_assoc in *. auto. }

            simpl in *; auto.
        }            

      (* RH is LolliR *)
      - inversion HeqcutF.
        subst. clear HeqcutF.
        clear IHA1. clear IHA2. clear Premise. 

        assert (eq1: S n + n0 < S n + S n0) by omega. 
        assert (eq2: S n + n0 = S n + n0) by omega.
        specialize (IHl (S n + n0) eq1
                        (S n) n0 eq2
                        B1 env (A1:: Delta1) Delta2 LH RH).
        clear eq1. clear eq2. clear LH. clear RH.
        destruct IHl as [z Last].

        assert (eq: z; [] ++ env ++ [A1] ++ Delta1 ++ Delta2 |- B1)
          by auto.

        apply exchange_with_env_l in eq.
        simpl in eq.
        apply (LolliR (z + length env) (env ++ Delta1 ++ Delta2)
                      A1 B1) in  eq.

        exists (S (z + length env)).
        auto.

      (* RH is WithL1 *)
      - inversion HeqcutF.
        subst. clear HeqcutF.
        apply element_in_app_head in backup.
        destruct backup as [Left | Right].

        * destruct Left as [t1 [t2 t3]].
          subst. discriminate.

        * destruct Right as [l t].
          subst.
          clear IHA1. clear IHA2.

          assert (eq: (A1 & B1 :: l) ++ [A -o B] ++ Delta2 =
                      Delta1 ++ [A -o B] ++ Delta2)
            by auto.
          apply app_inv_tail in eq.
          subst. clear HeqCF. clear Premise.

          assert (eq1: S n + n0 < S n + S n0) by omega. 
          assert (eq2: S n + n0 = S n + n0) by omega.
          apply (IHl (S n + n0) eq1
                          (S n) n0 eq2
                          C env (A1::l) Delta2 LH) in RH.
          clear eq1. clear eq2. clear LH. 
          destruct RH as [z Last].

          rewrite app_assoc in Last. 
          apply exchange_subset in Last.
          destruct Last as [m [_ Last]].
          rewrite <- app_assoc in Last. 
          simpl in *.
          apply (WithL1 m (l ++ env ++Delta2) A1 B1 C) in Last.

          assert (eq: S m;
                  ((A1 & B1 :: l) ++ env) ++ Delta2 |- C)
            by (repeat rewrite <- app_assoc in *; auto).
          apply exchange_subset in eq.
          destruct eq as [m' [_ eq]].
          rewrite <- app_assoc in *.
          simpl in *.
          exists m'; auto.

      (* RH is WithL2 *)
      - inversion HeqcutF.
        subst. clear HeqcutF.
        apply element_in_app_head in backup.
        destruct backup as [Left | Right].

        * destruct Left as [t1 [t2 t3]].
          subst. discriminate.

        * destruct Right as [l t].
          subst.
          clear IHA1. clear IHA2.

          assert (eq: (A1 & B1 :: l) ++ [A -o B] ++ Delta2 =
                      Delta1 ++ [A -o B] ++ Delta2)
            by auto.
          apply app_inv_tail in eq.
          subst. clear HeqCF. clear Premise.

          assert (eq1: S n + n0 < S n + S n0) by omega. 
          assert (eq2: S n + n0 = S n + n0) by omega.
          apply (IHl (S n + n0) eq1
                          (S n) n0 eq2
                          C env (B1::l) Delta2 LH) in RH.
          clear eq1. clear eq2. clear LH. 
          destruct RH as [z Last].

          rewrite app_assoc in Last. 
          apply exchange_subset in Last.
          destruct Last as [m [_ Last]].
          rewrite <- app_assoc in Last. 
          simpl in *.
          apply (WithL2 m (l ++ env ++Delta2) A1 B1 C) in Last.

          assert (eq: S m;
                  ((A1 & B1 :: l) ++ env) ++ Delta2 |- C)
            by (repeat rewrite <- app_assoc in *; auto).
          apply exchange_subset in eq.
          destruct eq as [m' [_ eq]].
          rewrite <- app_assoc in *.
          simpl in *.
          exists m'; auto.

      (* RH is WithR *)
      - subst.
        assert (eq1: S n + n0 < S n + S n0) by omega. 
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1 (S n) n0 eq2
                   A1 env Delta1 Delta2 LH) in RH1.
        apply (IHl (S n + n0) eq1 (S n) n0 eq2
                   B1 env Delta1 Delta2 LH) in RH2.
        destruct RH1 as [z1 RH1].
        destruct RH2 as [z2 RH2].

        apply (level_depth
                 z1 (env ++ Delta1 ++ Delta2) A1
                 z2 (env ++ Delta1 ++ Delta2) B1 RH1) in RH2.
        destruct RH2 as [k [H1 H2]].
        apply (WithR k (env ++ Delta1 ++ Delta2) A1 B1 H1) in H2.

        exists (S k); auto.

      (* RH is OplusL *)
      - inversion HeqcutF.
        subst.
        apply element_in_app_head in backup.
        destruct backup as [L | R].

        * destruct L as [L1 [L2 L3]].
          discriminate.

        * destruct R as [l R].
          subst.
          assert (eq: (A1 # B1 :: l)
                        ++ [A -o B] ++ Delta2 =
                      Delta1 ++ [A -o B] ++ Delta2)
            by auto.
          apply app_inv_tail in eq.
          subst.
          clear HeqCF. clear HeqcutF. clear Premise.

          assert (eq1: S n + n0 < S n + S n0) by omega. 
          assert (eq2: S n + n0 = S n + n0) by omega.
          assert (RH1': n0; (A1 :: l) ++ [A -o B] ++ Delta2
                            |- C) by auto.
          assert (RH2': n0; (B1 :: l) ++ [A -o B] ++ Delta2
                            |- C) by auto.
          apply (IHl (S n + n0) eq1 (S n) n0 eq2
                     C env (A1::l) Delta2 LH) in RH1'.
          apply (IHl (S n + n0) eq1 (S n) n0 eq2
                     C env (B1::l) Delta2 LH) in RH2'.
          destruct RH1' as [z1 RH1'].
          destruct RH2' as [z2 RH2'].

          clear RH1. clear RH2.
          rewrite app_assoc in RH1'.
          rewrite app_assoc in RH2'.
          apply exchange_subset in RH1'.
          destruct RH1' as [m1 [ _ RH1]].
          apply exchange_subset in RH2'.
          destruct RH2' as [m2 [ _ RH2]].
          rewrite <- app_assoc in *.
          simpl in *.

          apply (level_depth
                   m1 (A1::l ++ env ++ Delta2) C
                   m2 (B1::l ++ env ++ Delta2) C RH1)
            in RH2.
          destruct RH2 as [k [H1 H2]].
          apply (OplusL k (l ++ env ++ Delta2)
                        A1 B1 C H1) in H2.
          assert (eq: S k;
                  (A1 # B1 :: l) ++ env ++ Delta2
                  |- C) by auto.
          rewrite app_assoc in eq. 
          apply exchange_subset in eq.
          destruct eq as [m [ _ H]].
          rewrite <- app_assoc in H.
          simpl in *.
          exists m; auto.
          

      (* RH is OplusR1 *)
      - subst. 
        clear Premise.
        
        assert (eq1: S n + n0 < S n + S n0) by omega. 
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1 (S n) n0 eq2
                   A1 env Delta1 Delta2 LH) in RH.
        clear eq1. clear eq2. 

        destruct RH as [z H].
        exists (S z).
        constructor; auto.

      (* RH is OplusR2 *)
      - subst. 
        clear Premise.
        
        assert (eq1: S n + n0 < S n + S n0) by omega. 
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1 (S n) n0 eq2
                   B1 env Delta1 Delta2 LH) in RH.
        clear eq1. clear eq2. 

        destruct RH as [z H].
        exists (S z).
        apply (OplusR2 z (env ++ Delta1 ++ Delta2) A1 B1)
          in H; auto.
        
      (* RH is Perm *)
      - subst. clear HeqcutF.
        clear IHA1. clear IHA2. clear Premise.
        
        apply elements_in_app in HeqCF.

        {
          destruct HeqCF as [First | Remaining].

          (* First case *)
          - (* first some substitutions *)
            destruct First as [temp1 [l eq1]].
            subst.
            assert (eq1:
                      (Delta1 ++ [A0 -o B0])
                        ++ (l ++ [B1] ++ [A1] ++ Delta) =
                      (Delta1 ++ [A0 -o B0]) ++ Delta2).
            { repeat rewrite <- app_assoc in *. auto. }
            apply app_inv_head in eq1.
            subst. clear temp1. clear backup.

            repeat rewrite <- app_assoc in *.
            assert (eq1: S n + n0 < S n + S n0) by omega. 
            assert (eq2: S n + n0 = S n + n0) by omega.
            
            specialize (IHl (S n + n0) eq1
                            (S n) n0 eq2
                            C env Delta1
                            (l ++ [A1] ++ [B1] ++ Delta)
                            LH RH).
            clear eq1. clear eq2. clear LH. clear RH.
            destruct IHl as [z Last].

            assert (eq1:
                      z;
                    (env ++ Delta1 ++ l)
                      ++ [A1] ++ [B1] ++ Delta
                    |- C).
            { repeat rewrite <- app_assoc in *. auto. }

            apply (Perm z (env ++ Delta1 ++ l) Delta
                        A1 B1 C) in eq1.

            repeat rewrite <- app_assoc in *.

            exists (S z).
            auto.

            
          - (* other cases *)
            destruct Remaining as [Current | Remaining].

            (* Second Case *)
            + destruct Current as [temp1 [eq1 eq2]].
              subst. clear backup.
            
            assert (eq1: S n + n0 < S n + S n0) by omega. 
            assert (eq2: S n + n0 = S n + n0) by omega.
            assert (RH': n0; (Delta1 ++ [A1])
                               ++ [A0 -o B0] ++ Delta |- C)
                   by (repeat rewrite <- app_assoc in *; auto).
            
            specialize (IHl (S n + n0) eq1
                            (S n) n0 eq2
                            C env (Delta1 ++ [A1])
                            Delta
                            LH RH').
            clear eq1. clear eq2. clear LH. clear RH. clear RH'.
            destruct IHl as [z Last].

            exists z. 
            repeat rewrite <- app_assoc in *; auto.

            (* other cases *)
            + destruct Remaining as [Current | Final].

              (* Third Case *)
              * destruct Current as [temp1 [eq1 eq2]].
                subst. clear backup.
                assert (eq1: S n + n0 < S n + S n0) by omega. 
                assert (eq2: S n + n0 = S n + n0) by omega.
            
                specialize (IHl (S n + n0) eq1
                                (S n) n0 eq2
                                C env Gamma
                                ([B1] ++ Delta2)
                                LH RH).
                clear eq1. clear eq2. clear LH. clear RH. 
                destruct IHl as [z Last].
                
                exists z. 
                repeat rewrite <- app_assoc in *; auto.

              (* Fourth Case *)
              * (* some substs first *)
                destruct Final as [temp1 [l eq1]].
                subst.

                assert (eq1:
                          (Gamma ++ B1 :: A1 :: l)
                                ++ ([A0 -o B0] ++ Delta2) =
                          Delta1 ++ (A0 -o B0 :: Delta2))
                  by (repeat rewrite <- app_assoc in *; auto).

                apply app_inv_tail in eq1.
                subst. clear backup. clear temp1. 

                repeat rewrite <- app_assoc in *.
                assert (eq1: S n + n0 < S n + S n0) by omega. 
                assert (eq2: S n + n0 = S n + n0) by omega.
                assert (RH': n0;
                        (Gamma ++ [A1] ++ [B1] ++ l)
                          ++ [A0 -o B0] ++ Delta2 |- C)
                  by (repeat rewrite <- app_assoc in *; auto).

                specialize (IHl (S n + n0) eq1
                                (S n) n0 eq2
                                C env
                                (Gamma ++ [A1] ++ [B1] ++ l)
                                Delta2
                                LH RH').
                clear eq1. clear eq2. clear LH.
                clear RH. clear RH'.
                destruct IHl as [z Last].
                
                assert (eq1:
                          z;
                        (env ++ Gamma)
                          ++ [A1] ++ [B1] ++ l ++ Delta2
                    |- C).
            { repeat rewrite <- app_assoc in *. auto. }

            apply (Perm z (env ++ Gamma) (l ++ Delta2)
                        A1 B1 C) in eq1.

            repeat rewrite <- app_assoc in *.

            exists (S z).
            auto.
        }
    }

  (* LH is WithL1 *)
  * intros RH.
    subst. clear IHA1. clear IHA2.
      
    assert (eq1: n + m < S n + m) by omega.
    assert (eq2: n + m = n + m) by omega.
    specialize (IHl (n + m) eq1
                    n m  eq2
                    C
                    (A0 :: Gamma)
                    Delta1 Delta2 LH RH
               ).
    clear eq1. clear eq2. clear RH. clear LH.
    destruct IHl as [z IHl].

    assert (eq: z; A0:: Gamma ++ Delta1
                 ++ Delta2 |- C) by auto.

    apply (WithL1 z (Gamma ++ Delta1 ++ Delta2)
                   A0 B0 C)
      in eq.

    exists (S z).
    assert (H: S z;
            ([A0 & B0] ++ Gamma)
              ++ Delta1 ++ Delta2 |- C) by auto.
    auto.

  (* LH is WithL2 *)
  * intros RH.
    subst. clear IHA1. clear IHA2.
      
    assert (eq1: n + m < S n + m) by omega.
    assert (eq2: n + m = n + m) by omega.
    specialize (IHl (n + m) eq1
                    n m  eq2
                    C
                    (B0 :: Gamma)
                    Delta1 Delta2 LH RH
               ).
    clear eq1. clear eq2. clear RH. clear LH.
    destruct IHl as [z IHl].

    assert (eq: z; B0:: Gamma ++ Delta1
                 ++ Delta2 |- C) by auto.

    apply (WithL2 z (Gamma ++ Delta1 ++ Delta2)
                   A0 B0 C)
      in eq.

    exists (S z). auto.

  (* LH is WithR *)
  * discriminate. 

  (* LH is OplisL *)
  * intros RH.
    subst. clear IHA1. clear IHA2.
      
    assert (eq1: n + m < S n + m) by omega.
    assert (eq2: n + m = n + m) by omega.
    assert (RH': m; Delta1 ++ [A -o B] ++ Delta2 |- C)
           by auto.
    apply (IHl (n + m) eq1
                    n m  eq2
                    C
                    (A0 :: Gamma)
                    Delta1 Delta2 LH1) in RH.
    apply (IHl (n + m) eq1
                    n m  eq2
                    C
                    (B0 :: Gamma)
                    Delta1 Delta2 LH2) in RH'.
    clear eq1. clear eq2. clear LH1. clear LH2.
    destruct RH as [z RH].
    destruct RH' as [z' RH'].

    assert (H1: z; A0 :: Gamma
                     ++ Delta1 ++ Delta2 |- C)
      by auto.
    assert (H2: z'; B0 :: Gamma
                     ++ Delta1 ++ Delta2 |- C)
      by auto.

    apply (level_depth
             z (A0 :: Gamma ++ Delta1 ++ Delta2) C
             z' (B0 :: Gamma ++ Delta1 ++ Delta2) C
             H1) in H2.
    destruct H2 as [k [H H']].

    apply (OplusL k (Gamma ++ Delta1 ++ Delta2)
                  A0 B0 C H) in H'.

    exists (S k).
    auto.

  (* LH is OplusR1 *)
  * discriminate.

  (* LH is OplusR2 *)
  * discriminate. 

  (* LH is Perm *)
  * intros.
    clear IHA1. clear IHA2. 
    assert (eq1: n + m < l) by omega.
    assert (eq2: n + m = n + m) by omega.
    specialize (IHl (n + m) eq1 n m eq2
                    C (Gamma ++ [A0] ++ [B0] ++ Delta)
                    Delta1 Delta2
                    LH
                    H
               ).
    destruct IHl as [z Hyp].
    exists (S z).
    repeat rewrite <- app_assoc in *.
    constructor; auto.
Qed.