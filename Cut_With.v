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

Theorem cut_with :
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
      (n; Gamma |- (A & B))
      ->
      (m; Delta1 ++ [A & B] ++ Delta2 |- C)
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
  remember (A & B) as cutF.

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
    assert (RH' : m; [] ++ Delta1 ++ [A & B]
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
  * discriminate. 

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
  * inversion HeqcutF.
    subst. clear HeqcutF.
    intros RH.
    pose proof (WithR n Gamma A B LH1 LH2).
    rename H into LH.

    remember (Delta1 ++ [A & B] ++ Delta2) as CF.
    {
      destruct RH.

      (* RH is OneL *)
      - assert (backup: One :: Gamma0 =
                        Delta1
                          ++ [A & B]
                          ++ Delta2) by auto.

        apply element_in_app_head in HeqCF.

        destruct HeqCF as [Left | Right].

        * destruct Left as [t1 [t2 t3]].
          discriminate.

        * destruct Right as [l H].
          clear IHA1. clear IHA2.
          subst.

          assert(eq: (One :: l) ++ [A & B]
                         ++ Delta2 =
                     Delta1 ++ [A & B] ++ Delta2)
            by auto.
          apply app_inv_tail in eq.
          subst. clear backup.
          
          assert (eq1: S n + n0 < S n + S n0) by omega.
          assert (eq2: S n + n0 = S n + n0) by omega.
          specialize (IHl (S n + n0) eq1 (S n) n0 eq2
                    A0 Gamma l Delta2 LH RH).
          clear eq1. clear eq2. clear RH. clear LH.

          destruct IHl as [z H].
          apply OneL in H.
          assert (eq: S z; [] ++ [One] ++ Gamma
                              ++ l
                              ++ Delta2 |- A0)
            by auto.
          apply exchange_with_env_r in eq.
          assert (Hyp:
                    (S z + length Gamma);
                  Gamma ++ ([One] ++ l)
                      ++ Delta2 |- A0) by auto.
          
          exists (S z + length Gamma); auto.


      (* RH is OneR *)
      - simpl in *.
        apply app_cons_not_nil in HeqCF.
        destruct HeqCF. 

      (* RH is Atom *)
      - apply app_singleton in HeqCF.
        destruct HeqCF as [t1 [t2 t3]].
        subst.

        exists (S n).
        rewrite app_nil_r.
        constructor; auto.

      (* RH is TensorL *)
      - inversion HeqCF.
        apply element_in_app_head in HeqCF.

        destruct HeqCF as [Left | Right].

        * destruct Left as [t1 [t2 t3]].
          discriminate.

        * destruct Right as [l H].
          subst.
          assert (eq: (A0 ** B0 :: l)
                        ++ [A & B] ++ Delta2 =
                      Delta1 ++ [A & B] ++ Delta2)
            by auto.
          apply app_inv_tail in eq.
          subst. 

          assert (eq1: S n + n0 < S n + S n0) by omega.
          assert (eq2: S n + n0 = S n + n0) by omega.
          specialize (IHl (S n + n0) eq1 (S n) n0 eq2
                          C Gamma
                          (A0::B0::l)
                          Delta2 LH RH).
          clear eq1. clear eq2. clear RH. clear LH.

          destruct IHl as [z H].

          rewrite app_assoc in H.
          apply exchange_subset in H.
          destruct H as [m [ _ H]].

          assert( eq: m;
                  [A0] ++ [B0]
                       ++ l ++ Gamma ++ Delta2 |- C)
            by (repeat rewrite <- app_assoc in *; auto).
          simpl in eq.

          apply (TensorL m (l ++ Gamma
                              ++ Delta2) A0 B0 C)
            in eq.

          assert (eq': S m;
                  ((A0 ** B0 :: l) ++ Gamma)
                    ++ Delta2 |- C)
            by (repeat rewrite <- app_assoc in *; auto).

          apply exchange_subset in eq'.
          destruct eq' as [k [ _ Final]].
          rewrite <- app_assoc in Final.

          exists k; auto.          

      (* RH is TensorR *)
      - (* cleaning *)
        clear IHA1. clear IHA2.
        inversion HeqCF as [backup].

        

        (* some pre-processing *)
        assert (eq1: S n + n0 < S n + S n0) by omega. 
        assert (eq2: S n + n0 = S n + n0) by omega.    
        specialize (IHl (S n + n0) eq1 (S n) n0 eq2).
        clear eq1. clear eq2.

        (* We go by cases, since *)
        (* A & B could be in RH1 or RH2 *)
        apply element_in_app in HeqCF.
        {
          destruct HeqCF as [inEnv1 | inEnv2].

          (* on the left *)
          - destruct inEnv1 as [t1 [t2 [l t3]]].
            subst. clear t1. clear t2.

            (* one more infere&substitute *)
            assert (eq: (Delta1 ++ [A & B]) ++ (l ++ env2) =
                        (Delta1 ++ [A & B]) ++ Delta2).
            { repeat rewrite <- app_assoc in *. auto. }
            apply app_inv_head in eq. subst. clear backup.
            
            specialize (IHl A0 Gamma Delta1 l LH RH1).
            clear LH. clear RH1.
            destruct IHl as [z LH].

            apply (level_depth z (Gamma ++ Delta1 ++ l) A0
                               n0 env2 B0 LH) in RH2.
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
            assert (eq: (env1 ++ l) ++ ([A & B] ++ Delta2) =
                        Delta1 ++ (A & B :: Delta2))
              by (repeat rewrite <- app_assoc in *; auto). 
            apply app_inv_tail in eq. subst.
            clear backup.
            
            specialize (IHl B0 Gamma l Delta2 LH RH2).
            clear LH. clear RH2.
            destruct IHl as [z LH].

            apply (level_depth z (Gamma ++ l ++ Delta2) B0
                               n0 env1 A0 LH) in RH1.
            clear LH.
            destruct RH1 as [k [RH LH]].

            pose proof (TensorR k env1 A0
                                (Gamma ++ l ++ Delta2) B0
                                LH RH).
            assert (eq: S k; (env1 ++ Gamma) ++ l ++ Delta2
                           |- (A0 ** B0))
              by (rewrite <- app_assoc; auto ).
            apply exchange_subset in eq.
            destruct eq as [m [temp final]]. clear temp.
            exists m.
            repeat rewrite <- app_assoc in *; auto.
        }

        (* RH is LolliL *)
      - inversion HeqCF.
        subst. 
        (* we need to proceed by cases *)
        assert (eq: (A0 -o B0 :: env1) ++ env2 =
                    Delta1 ++ [A & B] ++ Delta2) by auto.
        apply element_in_app in eq.
        {
          destruct eq as [inLeft | inRight].
          
          (* on the left *)
          - destruct inLeft as [t1 [t2 [l t3]]].
            clear t1. clear t2.

            (* we have two more cases: reduce or commute *)
            assert (eq: [A0 -o B0] ++ env1 =
                        Delta1 ++ [A & B] ++ l) by auto.
            apply element_in_app in eq.

            {
              destruct eq as [reduction | commute].

              (* reduction case *)
              - destruct reduction as [_ [_ [l' t]]].
              apply app_singleton in t.
              destruct t as [t1 [t2 t4]].
              discriminate.
               
              (* commute case *)
              - destruct commute as [t1 [t2 [l' t4]]].
                clear t1. clear t2. clear IHA1. clear IHA2.
                
                (* some substitutions *)
                subst.
                assert (eq: (A0 -o B0 :: l')
                              ++ ([A & B] ++ l) =
                            Delta1 ++ ([A & B] ++ l))
                  by auto.
                apply app_inv_tail in eq.
                subst. clear t3. 
                assert (eq: ([A0 -o B0]
                               ++ l'
                               ++ [A & B])
                              ++ l ++ env2 =
                            ([A0 -o B0] ++ l' ++ [A & B])
                              ++ Delta2).
                { repeat rewrite <- app_assoc in *. auto. }
                apply app_inv_head in eq.
                subst. clear HeqCF. clear H0.
                
                assert (eq1: S n + n0 < S n + S n0) by omega. 
                assert (eq2: S n + n0 = S n + n0) by omega.
                specialize (IHl (S n + n0) eq1
                                (S n) n0 eq2
                                A0 Gamma l' l LH RH1).
                clear eq1. clear eq2. clear LH. clear RH1.
                destruct IHl as [z Last].

                apply (level_depth z (Gamma ++ l' ++ l) A0
                                   n0 (B0::env2) C Last)
                  in RH2.

                destruct RH2 as [k [First Second]].
                pose proof (LolliL k (Gamma ++ l' ++ l)
                                   A0
                                   env2 B0 C First Second).

                assert(eq: S k; [] ++ [A0 -o B0] ++ Gamma
                                   ++ l' ++ l ++ env2 |- C).
                { simpl in *.
                  repeat rewrite <- app_assoc in *.
                  auto. }

                apply exchange_with_env_r in eq.

                exists (S k + length Gamma); auto.
            }

          (* on the right *)
          - destruct inRight as [t1 [t2 [l t3]]].
            clear t1. clear t2. clear IHA1. clear IHA2.

            (* first some subst, to simplify *)
            subst.
            assert (eq: (A0 -o B0 :: env1 ++ l)
                          ++ (A & B :: Delta2)
                        =
                        Delta1 ++ (A & B :: Delta2)).
            { simpl in *.
              repeat rewrite <- app_assoc in *. auto. }
            apply app_inv_tail in eq.
            subst. clear HeqCF. 

            assert (eq1: S n + n0 < S n + S n0) by omega. 
            assert (eq2: S n + n0 = S n + n0) by omega.
            specialize (IHl (S n + n0) eq1
                            (S n) n0 eq2
                            C Gamma (B0::l) Delta2 LH RH2).
            clear eq1. clear eq2. clear LH. clear RH2.
            destruct IHl as [z Last].

            assert (eq1: z; [] ++ Gamma ++ [B0]
                               ++ l ++ Delta2 |- C)
              by auto.

            apply exchange_with_env_l in eq1.
            simpl in eq1. 
            apply (level_depth
                     (z + length Gamma)
                     (B0 :: Gamma ++ l ++ Delta2) C
                     n0 env1 A0 eq1) in RH1.
            clear eq1. clear Last.
            
            destruct RH1 as [k [RH LH]].

            pose proof (LolliL k env1 A0
                               (Gamma ++ l ++ Delta2) B0 C
                               LH RH).

            assert (eq1: S k; (([A0 -o B0] ++ env1)
                                 ++ Gamma) ++ l ++ Delta2
                              |- C).
            { repeat rewrite <- app_assoc in *.
              simpl. auto. }

            apply exchange_subset in eq1.
            destruct eq1 as [m [temp Final]].

            exists m.

            assert (eq1:  m; Gamma
                               ++ ([A0 -o B0] ++ env1 ++ l)
                               ++ Delta2 |- C).
            { repeat rewrite <- app_assoc in *. auto. }

            simpl in *; auto.
        }            

      (* RH is LolliR *)
      - subst. clear IHA1. clear IHA2.
        
        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1
                   (S n) n0 eq2
                   B0
                   Gamma
                   (A0::Delta1) Delta2 LH) in RH.
        destruct RH as [z RH]. clear LH.
        clear eq1. clear eq2.

        rewrite app_assoc in RH.
        apply exchange_subset in RH.
        destruct RH as [m [ _  H]].
        rewrite <- app_assoc in H.
        simpl in *.
        apply (LolliR m (Delta1 ++ Gamma ++ Delta2) A0 B0)
          in H.
        rewrite app_assoc in H.
        apply exchange_subset in H.
        destruct H as [m0 [_ H]].
        rewrite <- app_assoc in H.
        exists m0; auto.

      (* RH is WithL1 -- MAY REDUCE *)
      - inversion HeqCF as [backup].
        apply element_in_app_head in HeqCF.
        destruct HeqCF as [Left | Right].

        (* Reduce *)
        + destruct Left as [t1 [t2 t3]].
          inversion t2.
          subst. clear t2. clear backup.
          clear IHl. clear IHA2.
          
          assert (RH': n0; [] ++ A :: Delta2 |- C)
            by auto.
          apply (IHA1 n n0 C Gamma [] Delta2
                      LH1) in RH'.

          destruct RH' as [z H].
          exists z; auto.

        (* Commute *)
        + destruct Right as [l t].
          subst.

          assert (eq: (A0 & B0 :: l)
                        ++ [A & B] ++ Delta2 =
                      Delta1 ++ A & B :: Delta2)
            by auto.
          apply app_inv_tail in eq.
          subst. clear backup.

          assert (eq1: S n + n0 < S n + S n0) by omega.
          assert (eq2: S n + n0 = S n + n0) by omega.
          apply (IHl (S n + n0) eq1
                     (S n) n0 eq2
                     C
                     Gamma
                     (A0::l) Delta2 LH) in RH.
          destruct RH as [z H].
          clear LH. clear eq1. clear eq2.

          rewrite app_assoc in H.
          apply exchange_subset in H.
          destruct H as [m [ _ H]].
          rewrite <- app_assoc in H.
          simpl in *.
          apply (WithL1 m (l ++ Gamma ++ Delta2)
                        A0 B0 C) in H.

          assert(H': S m; (A0 & B0 :: l)
                            ++ Gamma
                            ++ Delta2 |- C)
            by auto.
          rewrite app_assoc in H'.
          apply exchange_subset in H'.
          destruct H' as [m0 [_ H']].
          rewrite <- app_assoc in H'.
          exists m0; auto.

      (* RH is WithL2 -- MAY REDUCE *)
      - inversion HeqCF as [backup].
        apply element_in_app_head in HeqCF.
        destruct HeqCF as [Left | Right].

        (* Reduce *)
        + destruct Left as [t1 [t2 t3]].
          inversion t2.
          subst. clear t2. clear backup.
          clear IHl. clear IHA1.
          
          assert (RH': n0; [] ++ B :: Delta2 |- C)
            by auto.
          apply (IHA2 n n0 C Gamma [] Delta2
                      LH2) in RH'.

          destruct RH' as [z H].
          exists z; auto.

        (* Commute *)
        + destruct Right as [l t].
          subst.

          assert (eq: (A0 & B0 :: l)
                        ++ [A & B] ++ Delta2 =
                      Delta1 ++ A & B :: Delta2)
            by auto.
          apply app_inv_tail in eq.
          subst. clear backup.

          assert (eq1: S n + n0 < S n + S n0) by omega.
          assert (eq2: S n + n0 = S n + n0) by omega.
          apply (IHl (S n + n0) eq1
                     (S n) n0 eq2
                     C
                     Gamma
                     (B0::l) Delta2 LH) in RH.
          destruct RH as [z H].
          clear LH. clear eq1. clear eq2.

          rewrite app_assoc in H.
          apply exchange_subset in H.
          destruct H as [m [ _ H]].
          rewrite <- app_assoc in H.
          simpl in *.
          apply (WithL2 m (l ++ Gamma ++ Delta2)
                        A0 B0 C) in H.

          assert(H': S m; (A0 & B0 :: l)
                            ++ Gamma
                            ++ Delta2 |- C)
            by auto.
          rewrite app_assoc in H'.
          apply exchange_subset in H'.
          destruct H' as [m0 [_ H']].
          rewrite <- app_assoc in H'.
          exists m0; auto.

      (* RH is WithR *)
      - subst.
        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        specialize (IHl (S n + n0) eq1 (S n) n0 eq2).
        clear IHA1. clear IHA2. clear LH1. clear LH2.
        clear eq1. clear eq2.

        apply (IHl A0 Gamma Delta1 Delta2 LH) in RH1.
        apply (IHl B0 Gamma Delta1 Delta2 LH) in RH2.
        clear LH. clear IHl.

        destruct RH1 as [z1 RH1].
        destruct RH2 as [z2 RH2].

        apply (level_depth
                 z1 (Gamma ++ Delta1 ++ Delta2) A0
                 z2 (Gamma ++ Delta1 ++ Delta2) B0
                 RH1) in RH2.
        clear RH1.
        destruct RH2 as [k [H1 H2]].

        apply (WithR k (Gamma ++ Delta1 ++ Delta2)
                     A0 B0 H1) in H2.
        exists (S k); auto.

      (* RH is OplusL *)
      - subst. clear LH1. clear LH2.
        clear IHA1. clear IHA2. 
        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        specialize (IHl (S n + n0) eq1
                        (S n) n0 eq2 C Gamma).
        clear eq1. clear eq2.
        
        inversion HeqCF as [backup].
        apply element_in_app_head in HeqCF.
        {
          destruct HeqCF as [L | R].
          - destruct L as [t1 [t2 t3]].
            discriminate. 
            
          - destruct R as [l t].
            subst.
            assert (eq: (A0 # B0 :: l)
                          ++ [A & B] ++ Delta2 =
                        Delta1
                          ++ A & B :: Delta2) by auto.
            apply app_inv_tail in eq.
            subst. clear backup.

            apply (IHl (A0::l) Delta2 LH) in RH1.
            apply (IHl (B0::l) Delta2 LH) in RH2.
            clear LH.
            destruct RH1 as [z1 RH1].
            destruct RH2 as [z2 RH2].
            rewrite app_assoc in *.
            apply exchange_subset in RH1.
            apply exchange_subset in RH2.
            destruct RH1 as [m1 [_ RH1]].
            destruct RH2 as [m2 [_ RH2]].
            rewrite <- app_assoc in *.

            apply (level_depth
                     m1 (A0:: l ++ Gamma ++ Delta2) C
                     m2 (B0:: l ++ Gamma ++ Delta2) C
                     RH1) in RH2.
            clear RH1.
            destruct RH2 as [k [H1 H2]].

            apply (OplusL k (l ++ Gamma ++ Delta2)
                          A0 B0 C H1) in H2.

            assert (eq: S k; ((A0 # B0 :: l)
                                ++ Gamma)
                               ++ Delta2 |- C)
              by (repeat rewrite <- app_assoc in *; auto).

            apply exchange_subset in eq.
            destruct eq as [m [_ H]].
            rewrite <- app_assoc in *.

            exists m; auto.
        }

      (* RH is OplusR1 *)
      - subst.
        clear LH1. clear LH2.
        clear IHA1. clear IHA2.
        
        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1
                   (S n) n0 eq2
                   A0
                   Gamma
                   Delta1 Delta2 LH) in RH.
        destruct RH as [z RH]. clear LH.
        clear eq1. clear eq2.

        exists (S z); constructor; auto.

      (* RH is OplusR2 *)
      - subst.
        clear LH1. clear LH2.
        clear IHA1. clear IHA2.
        
        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1
                   (S n) n0 eq2
                   B0
                   Gamma
                   Delta1 Delta2 LH) in RH.
        destruct RH as [z RH]. clear LH.
        clear eq1. clear eq2.

        exists (S z).
        apply OplusR2; auto.

      (* RH is Perm *)
      - clear LH1. clear LH2.
        clear IHA1. clear IHA2.
        
        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        specialize (IHl (S n + n0) eq1
                        (S n) n0 eq2 C Gamma).
        clear eq1. clear eq2.

        inversion HeqCF as [backup].
        apply elements_in_app in HeqCF.

        { destruct HeqCF as [First | Remaining].

          (* First *)
          - destruct First as [_ [l t]].
            subst.
            assert (eq: (Delta1 ++ [A & B])
                          ++ l ++ B0 :: A0 :: Delta =
                        (Delta1 ++ [A & B]) ++ Delta2)
              by (repeat rewrite <- app_assoc in *; auto).
            
            apply app_inv_head in eq.
            subst. clear backup.

            repeat rewrite <- app_assoc in RH.

            apply (IHl Delta1
                       (l ++ [A0] ++ [B0] ++ Delta)
                       LH)
              in RH.
            destruct RH as [z H].
            rewrite app_assoc in H.
            rewrite app_assoc in H.
            
            apply (Perm z ((Gamma ++ Delta1) ++ l)
                        Delta A0 B0 C) in H.
            repeat rewrite <- app_assoc in *.

            exists (S z); auto.

            
          - destruct Remaining as [Second | Remaining].

            (* Second *)
            + destruct Second as [t1 [t2 t3]].
              subst. clear backup.
              rewrite app_assoc in RH.
              apply (IHl (Delta1 ++ [A0])
                         Delta LH) in RH.
              destruct RH as [z H].
              rewrite <- app_assoc in *.
              exists z; auto.

            + destruct Remaining as [Third | Fourth].

              * destruct Third as [t1 [t2 t3]].
                subst. clear backup.
                apply (IHl Gamma0 ([B0] ++ Delta2)
                           LH) in RH.
                destruct RH as [z H].
                rewrite <- app_assoc.
                exists z; auto.

              * destruct Fourth as [_ [l t]].
                subst.
                assert (eq: (Gamma0
                              ++ B0 :: A0 :: l)
                              ++ A & B::Delta2 =
                                     Delta1
                                       ++ A & B :: Delta2)
                  by (repeat rewrite <- app_assoc in *;
                      auto).
                apply app_inv_tail in eq.
                subst. clear backup.

                rewrite app_assoc in RH.
                rewrite app_assoc in RH.
                rewrite app_assoc in RH.
                apply (IHl
                         (((Gamma0 ++ [A0]) ++ [B0]) ++ l)
                         Delta2
                         LH) in RH.
                destruct RH as [z H].
                repeat rewrite <- app_assoc in *.
                rewrite app_assoc in *.
                apply (Perm z
                            (Gamma ++ Gamma0)
                            (l ++ Delta2)
                            A0 B0 C) in H.
                exists (S z); auto.
        }
    }


  (* LH is OplusL *)
  * intros RH.
    subst. clear IHA1. clear IHA2.
      
    assert (eq1: n + m < S n + m) by omega.
    assert (eq2: n + m = n + m) by omega.
    assert (RH': m; Delta1 ++ [A & B] ++ Delta2 |- C)
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