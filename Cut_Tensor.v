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



Theorem cut_tensor :
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
      (n; Gamma |- (A ** B))
      ->
      (m; Delta1 ++ [A ** B] ++ Delta2 |- C)
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
  remember (A ** B) as cutF.

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
    assert (RH' : m; []
                       ++ Delta1 ++ [A ** B]
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
  * inversion HeqcutF.
    subst. clear HeqcutF.

    intros RH.
    remember (Delta1 ++ [A ** B] ++ Delta2) as RHEnv.

    (* We proceed by cases on RH *)
    { destruct RH.

      (* RH is OneL *)
      + subst.
          
        pose proof (TensorR n env1 A env2 B LH1 LH2).
        clear LH1. clear LH2.

        assert (eq: [One] ++ Gamma =
                    Delta1 ++ [A ** B] ++ Delta2)
          by auto.
        apply element_in_app in eq.
        destruct eq as [Left | Right].

        * destruct Left as [t1 [t2 [l t3]]].
          clear t1. clear t2.
          apply app_singleton in t3.
          destruct t3 as [t1 [t2 t3]].
          discriminate.

        * destruct Right as [t1 [t2 [l t3]]].
          clear t1. clear t2.
          subst.
          assert (eq: ([One] ++ l)
                        ++ [A ** B] ++ Delta2 =
                      Delta1 ++ [A ** B] ++ Delta2)
              by auto.
          apply app_inv_tail in eq.
          subst. clear HeqRHEnv.

          assert (eq1: S n + n0 < S n + S n0) by omega.
          assert (eq2: S n + n0 = S n + n0) by omega.
          specialize (IHl (S n + n0) eq1
                          (S n) n0 eq2
                          A0 (env1 ++ env2) l Delta2
                          H RH).
            clear eq1. clear eq2. clear RH. clear H.

            destruct IHl as [z Hyp].
            pose proof (OneL
                          z
                          ((env1 ++ env2) ++ l ++ Delta2)
                          A0 Hyp).
            assert (H': S z;
                    [] ++ [One] ++ (env1 ++ env2)
                       ++ l ++ Delta2 |- A0) by auto.
            apply exchange_with_env_r in H'.

            exists (S z + length (env1 ++ env2)).

            repeat rewrite <- app_assoc in *; auto.
          
      (* RH is OneR *)
      + apply app_cons_not_nil in HeqRHEnv.
        destruct HeqRHEnv.
          
      (* RH is Axiom *)
      + apply app_singleton in HeqRHEnv.
        destruct HeqRHEnv as [t1 [t2 t3]].
        subst.
        rewrite app_nil_r.
        exists (S n).
        constructor; auto.
            
      (* RH is TensorL *)
      + destruct Delta1.
        (* Here we have two cases: *)
        (* i) TensorL on cut formula (Delta1 = []) *)
        (* ii) TensorL not on cut form. (Delta1!=[]) *)
        
        (* i) we need to reduce *)
        * inversion HeqRHEnv.
          subst. clear HeqRHEnv. clear IHl.

          (* we first cut A *)
          assert (RH': n0;
                  [] ++ [A] ++ (B::Delta2) |- C)
            by auto.
          apply (IHA1 n n0 C env1 []
                     (B::Delta2) LH1)
            in RH'.
          clear RH. clear LH1.
          destruct RH' as [z RH].

          (* second, we cut B *)
          assert (RH': z;
                  env1 ++ [B] ++ Delta2 |-C)
            by auto.
          apply (IHA2 n z C env2 env1 Delta2
                     LH2) in RH'.
          clear RH. clear LH2.
          destruct RH' as [z' RH].

          rewrite app_assoc in RH.
          apply exchange_subset in RH.
          destruct RH as [m [t1 RH]].

          exists m; auto.
          

        (* ii) we need to commute *)
        * assert (eq: [A0 ** B0] ++ env =
                      (f :: Delta1)
                        ++ [A ** B]
                        ++ Delta2)
            by auto.
          apply element_in_app in eq.

          {
            destruct eq as [Left | Right].

            - destruct Left as [t1 [t2 [l t3]]].
              clear t1. clear t2.
              apply app_singleton in t3.
              destruct t3; discriminate.

            - destruct Right as [t1 [t2 [l t3]]].
              clear t1. clear t2. clear IHA1. clear IHA2.
              subst.
              assert (eq:
                        (A0 ** B0 :: l)
                          ++ [A ** B] ++ Delta2 =
                        (f :: Delta1)
                          ++ [A ** B] ++ Delta2)
                by auto.
              apply app_inv_tail in eq.
              inversion eq.
              subst. clear eq. clear HeqRHEnv.

              assert (Hyp:
                        n0;
                      (A0 :: B0 :: Delta1)
                        ++ [A ** B]
                        ++ Delta2 |- C) by auto.
              pose proof (TensorR n env1 A
                                  env2 B LH1 LH2).
              assert (eq1 : S n + n0 < S n + S n0)
                by omega.
              assert (eq2 : S n + n0 = S n + n0)
                by omega.
              specialize (IHl ((S n) + n0)
                              eq1 (S n) n0 eq2 C
                              (env1 ++ env2)
                              (A0::B0::Delta1)
                              Delta2 H RH
                         ).
              destruct IHl as [z IHl].

              rewrite app_assoc in IHl.

              apply exchange_subset in IHl.
              destruct IHl as [m [t1 Final]].

              simpl in Final.
              pose proof (TensorL
                            m
                            ((Delta1 ++ env1 ++ env2)
                               ++ Delta2) A0 B0 C Final).
              assert (eq:
                        S m;
                      [] ++ (([A0 ** B0]
                         ++ Delta1) ++ (env1 ++ env2))
                         ++ Delta2
                      |- C)
                by (repeat rewrite <- app_assoc in *;
                    auto).
              apply exchange_subset in eq.
              destruct eq as [k [temp1 temp2]].
              
              exists k.
              simpl in *.
              repeat rewrite <- app_assoc in *; auto.
          } 
                        
      (* RH is TensorR *)    
      + subst. clear IHA1. clear IHA2.

        (* We reapply TensorR - Coq undoes it *)
        pose proof (TensorR n env1 A env2 B LH1 LH2).
        rename H into LH.
        clear LH1.
        clear LH2.
          
        (* We now reason by cases *)
        (* depending on where the cutformula is: *)
        (* it's either in RH1 or RH2 *)
        inversion HeqRHEnv.
        apply element_in_app in H0.
        destruct H0.
        
        (* Cut formula on left premise of RH *)
        * destruct H as [t1 [t2 [l t3]]].
          subst. clear t1. clear t2.
          assert (eq:
                    (Delta1 ++ [A ** B])
                      ++ l ++ env3 =
                    (Delta1 ++ [A ** B])
                      ++ Delta2)
            by (repeat rewrite <- app_assoc in *; auto).
          apply app_inv_head in eq.
          subst. clear HeqRHEnv.
          
          (* We start using the IH on l *)
          assert (eq1: S n + n0 < S n + S n0)
            by omega.
          assert (eq2: S n + n0 = S n + n0)
            by omega.
          specialize (IHl (S n + n0) eq1
                          (S n) n0 eq2 A0
                          (env1 ++ env2)
                          Delta1 l LH RH1
                     ).
          clear eq1. clear eq2. clear RH1. clear LH.

          destruct IHl as [z Hyp].
          apply (level_depth
                   z ((env1 ++ env2) ++ Delta1 ++ l) A0
                   n0 env3 B0 Hyp) in RH2.
          destruct RH2 as [k [Hyp1 Hyp2]].

          exists (S k).
          
          apply (TensorR
                   k
                   ((env1 ++ env2) ++ Delta1 ++ l) A0
                   env3 B0 Hyp1) in  Hyp2.

          repeat rewrite <- app_assoc in *; auto.


        (* Cut formula on right premise of RH *)
        *
          (* We start using the IH on l *)
          specialize (IHl  ((S n) + n0)).
            
          assert (eq1: S n + n0 < S n + S n0)
            by omega.
          
          specialize (IHl eq1 (S n) n0).
          
          assert (eq2: S n + n0 = S n + n0)
            by omega.
          

          destruct H as [H' H ].
          destruct H as [Hextra H].
          destruct H as [l].
          inversion H as [env3Def].
          
          rewrite H in RH2.
          
          specialize
            (IHl eq2 B0 (env1 ++ env2)
                 l Delta2 LH RH2).

          destruct IHl.
          
          apply (level_depth
                   n0 env0 A0
                   x ((env1 ++ env2) ++ l ++ Delta2) B0
                   RH1) in H0.
          clear RH1. clear RH2. clear LH.
          clear Hextra. clear eq1. clear eq2. subst.
          clear env3Def.
          assert (eq: (env0 ++ l)
                        ++ [A ** B] ++ Delta2 =
                      Delta1 ++ [A ** B] ++ Delta2)
            by ( repeat rewrite <- app_assoc; auto ).
          apply app_inv_tail in eq.
          subst. clear HeqRHEnv. clear H'.
          destruct H0 as [k [RH1 RH2]].
          
          pose proof (TensorR
                        k env0 A0
                        ((env1 ++ env2)
                           ++ l ++ Delta2) B0
                        RH1 RH2).
          assert ( eq: S k;
                   (env0 ++ (env1 ++ env2))
                     ++ l ++ Delta2
                   |- (A0 ** B0))
            by ( repeat rewrite <- app_assoc in *;
                 auto ).
          apply exchange_subset in eq.
          destruct eq as [m [temp Final]].
          exists m.
          repeat rewrite <- app_assoc in *; auto.
          
      (* RH is LolliL *)
      + 
        (* We reapply TensorR - Coq undoes it *)
        pose proof (TensorR n env1 A env2 B LH1 LH2).
        rename H into LH.
        clear LH1. clear LH2. clear IHA1. clear IHA2.
        subst.
        
        (* we need to generate cases *)
        assert ([A0 -o B0] ++ env0 ++ env3 =
                Delta1 ++ [A ** B] ++ Delta2)
          by auto.
        rewrite app_assoc in H.
        apply element_in_app in H.
        destruct H as [Left | Right].
          
        * destruct Left as [t1 [t2 [l Hyp]]].
          clear t1. clear t2.
          inversion Hyp as [subst1].
          apply element_in_app in Hyp.
          {
            destruct Hyp as [LeftLeft | LeftRight].

            + destruct LeftLeft as [t1 [t2 [l' t3]]].
              simpl in *.
              destruct t1;[discriminate | destruct H].

            + destruct LeftRight as [t1 [t2 [l0 t3]]].
              subst. clear t1. clear t2.
              assert(eq1:  (A0 -o B0 :: l0) ++ (A ** B:: l) =
                           Delta1 ++ A ** B :: l)
                by (repeat rewrite <- app_assoc; auto ).
              apply app_inv_tail in eq1.
              subst. 
              assert(eq1: ([A0 -o B0] ++ l0 ++ [A ** B])
                            ++ l ++ env3 =
                          ([A0 -o B0] ++ l0 ++ [A ** B])
                            ++ Delta2)
                by (repeat rewrite <- app_assoc in *; auto ).
              apply app_inv_head in eq1.
              subst. clear subst1. clear HeqRHEnv.

              assert (eq1 : S n + n0 < S n + S n0) by omega.
              assert (eq2 : S n + n0 = S n + n0) by omega.
              specialize (IHl ((S n) + n0)
                              eq1 (S n) n0 eq2 A0
                              (env1 ++ env2)
                              l0 l LH RH1 ).
              clear eq1. clear eq2. clear RH1. clear LH.
              destruct IHl as [z IHl].

              apply (level_depth
                       z ((env1 ++ env2) ++ l0 ++ l) A0
                       n0 (B0::env3) C IHl) in RH2.
              clear IHl. destruct RH2 as [k [Hyp1 Hyp2]]. 

              pose proof (LolliL
                            k
                            ((env1 ++ env2) ++ l0 ++ l) A0
                            env3 B0 C Hyp1 Hyp2).
              assert (eq: S k;
                      ([A0 -o B0] ++ (env1 ++ env2))
                        ++ l0 ++ l ++ env3 |- C)
                by (repeat rewrite <- app_assoc in *; auto).
              apply exchange_subset in eq.
              destruct eq as [m [t1 Hyp]].

              exists m.

              repeat rewrite <- app_assoc in *; auto.

          }

        * destruct Right as [ _ [ _ [l t]]].
          subst. 
          assert (eq: ([A0 -o B0] ++ env0 ++ l)
                        ++ ([A ** B] ++ Delta2) = 
                      (Delta1) ++ ([A ** B] ++ Delta2))
            by ( repeat rewrite <- app_assoc; auto ).
          apply app_inv_tail in eq.
          subst. clear HeqRHEnv.
                
          assert (eq1: S n + n0 < S n + S n0) by omega.
          assert (eq2: S n + n0 = S n + n0) by omega.

          specialize (IHl (S n + n0) eq1
                          (S n) n0 eq2
                          C
                          (env1 ++ env2)
                          (B0 :: l) Delta2 LH RH2).
          clear eq1. clear eq2. clear LH. clear RH2. 
          destruct IHl as [z Hyp]. 

          assert (eq: z; [] ++ (env1 ++ env2) ++ [B0]
                            ++ l ++ Delta2 |- C)
            by auto.
          clear Hyp.
          apply exchange_with_env_l in eq.
          simpl in eq.
          apply (level_depth
                   n0 env0 A0
                   (z + length (env1 ++ env2))
                   (B0 :: (env1 ++ env2) ++ l ++ Delta2)
                   C RH1) in eq.
          clear RH1. 
          destruct eq as [k [Hyp1 Hyp2]].
          apply (LolliL
                   k env0 A0 
                   ((env1 ++ env2) ++ l ++ Delta2) B0 C Hyp1)
            in Hyp2.
          clear Hyp1.

          assert (Hyp: S k;
                  ((A0 -o B0 :: env0) ++ (env1 ++ env2))
                    ++ l ++ Delta2 |- C)
            by (repeat rewrite <- app_assoc in *; auto ).

          apply exchange_subset in Hyp.
          destruct Hyp as [m [_ Final]].

          repeat rewrite <- app_assoc in *.
          exists m; auto.

      (* RH is a LolliR *)
      + subst.

        (* We reapply TensorR - Coq undoes it *)
        pose proof (TensorR n env1 A env2 B LH1 LH2).
        rename H into LH.
        clear LH1. clear LH2.

        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        specialize (IHl (S n + n0) eq1
                        (S n) n0 eq2
                        B0
                        (env1 ++ env2)
                        (A0 :: Delta1)
                        Delta2
                        LH
                        RH
                   ).
        clear eq1. clear eq2.
          
        destruct IHl as [z IHl].
        
        assert (eq1: z;
                [] ++
                   (env1 ++ env2) ++ [A0] ++ Delta1 ++ Delta2
                |- B0
               ) by auto.

        apply exchange_with_env_l in eq1.
        simpl in eq1.
        
        pose proof (LolliR
                      (z + length (env1 ++ env2))
                      ((env1 ++ env2) ++ Delta1 ++ Delta2)
                      A0
                      B0
                      eq1
                   ).
        
        exists (S (z + length (env1 ++ env2))).
        assumption.

      (* RH is a WithL1 *)
      + clear IHA1. clear IHA2.
        assert (eq: [A0 & B0] ++ Gamma =
                    Delta1 ++ [A ** B] ++ Delta2)
          by auto.
        apply element_in_app in eq.
        {
          destruct eq as [Left | Right].
          
          - destruct Left as [_ [ _ [l Hyp]]].
            apply app_singleton in Hyp.
            destruct Hyp as [t1 [t2 t3]].
            subst.
            simpl in *. inversion HeqRHEnv.

          - destruct Right as [ _ [ _ [l Hyp]]].
            subst.
            assert (eq: (A0 & B0 :: l) ++ [A ** B] ++ Delta2
                             =
                             Delta1 ++ [A ** B] ++ Delta2)
              by auto.
            apply app_inv_tail in eq.
            subst. clear HeqRHEnv.

            apply (TensorR n env1 A env2 B LH1) in LH2.
            clear LH1. rename LH2 into LH.

            assert (eq1: S n + n0 < S n + S n0) by omega.
            assert (eq2: S n + n0 = S n + n0) by omega.
            specialize (IHl (S n + n0) eq1
                            (S n) n0 eq2
                            C
                            (env1 ++ env2)
                            (A0 ::l) Delta2 LH RH). 
            clear eq1. clear eq2. clear LH. clear RH.
            destruct IHl as [z Hyp].

            assert (eq: z; ((env1 ++ env2) ++ (A0 :: l))
                             ++ Delta2 |- C)
              by ( repeat rewrite <- app_assoc in *; auto ).

            apply exchange_subset in eq.
            destruct eq as [m [ _ Hyp']].

            repeat rewrite <- app_assoc in *.
            simpl in *.

            apply (WithL1 m (l ++ env1 ++ env2 ++ Delta2)
                          A0 B0 C) in Hyp'.

            assert (eq: S m; (([A0 & B0] ++ l) ++ (env1 ++ env2) )
                               ++ Delta2 |- C)
              by ( repeat rewrite <- app_assoc in *; auto ).

            apply exchange_subset in eq. 
            destruct eq as [m' [ _ Hyp'']].

            exists m'.
            repeat rewrite <- app_assoc in *; auto.
        }

      (* RH is a WithL2 *)
      + clear IHA1. clear IHA2.
        assert (eq: [A0 & B0] ++ Gamma =
                    Delta1 ++ [A ** B] ++ Delta2)
          by auto.
        apply element_in_app in eq.
        {
          destruct eq as [Left | Right].
          
          - destruct Left as [_ [ _ [l Hyp]]].
            apply app_singleton in Hyp.
            destruct Hyp as [t1 [t2 t3]].
            subst.
            simpl in *. inversion HeqRHEnv.

          - destruct Right as [ _ [ _ [l Hyp]]].
            subst.
            assert (eq: (A0 & B0 :: l) ++ [A ** B] ++ Delta2
                             =
                             Delta1 ++ [A ** B] ++ Delta2)
              by auto.
            apply app_inv_tail in eq.
            subst. clear HeqRHEnv.
            
            apply (TensorR n env1 A env2 B LH1) in LH2.
            clear LH1. rename LH2 into LH.

            assert (eq1: S n + n0 < S n + S n0) by omega.
            assert (eq2: S n + n0 = S n + n0) by omega.
            specialize (IHl (S n + n0) eq1
                            (S n) n0 eq2
                            C
                            (env1 ++ env2)
                            (B0 ::l) Delta2 LH RH). 
            clear eq1. clear eq2. clear LH. clear RH.
            destruct IHl as [z Hyp].

            assert (eq: z; ((env1 ++ env2) ++ (B0 :: l))
                             ++ Delta2 |- C)
              by ( repeat rewrite <- app_assoc in *; auto ).

            apply exchange_subset in eq.
            destruct eq as [m [ _ Hyp']].

            repeat rewrite <- app_assoc in *.
            simpl in *.

            apply (WithL2 m (l ++ env1 ++ env2 ++ Delta2)
                          A0 B0 C) in Hyp'.

            assert (eq: S m; (([A0 & B0] ++ l) ++ (env1 ++ env2) )
                               ++ Delta2 |- C)
              by ( repeat rewrite <- app_assoc in *; auto ).

            apply exchange_subset in eq. 
            destruct eq as [m' [ _ Hyp'']].

            exists m'.
            repeat rewrite <- app_assoc in *; auto.
        }

      (* RH is a WithR *)
      + subst. clear IHA1. clear IHA2.

        (* We reapply TensorR - Coq undoes it *)
        pose proof (TensorR n env1 A env2 B LH1 LH2).
        rename H into LH.
        clear LH1. clear LH2.

        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1
                   (S n) n0 eq2
                   A0 (env1 ++ env2) Delta1 Delta2
                   LH) in RH1. 
        apply (IHl (S n + n0) eq1
                   (S n) n0 eq2
                   B0 (env1 ++ env2) Delta1 Delta2
                   LH) in RH2.

        destruct RH1 as [z1 RH1].
        destruct RH2 as [z2 RH2].
        clear eq1. clear eq2. clear LH.

        apply (level_depth
                 z1 ((env1 ++ env2) ++ Delta1 ++ Delta2) A0
                 z2 ((env1 ++ env2) ++ Delta1 ++ Delta2) B0
                 RH1) in RH2.
        clear RH1.
        destruct RH2 as [k [H1 H2]].
        exists (S k).
        constructor; auto.
        
                   
      (* RH is a OplusL1 *)
      + clear IHA1. clear IHA2.
        assert (H: [A0 # B0] ++ Gamma =
                Delta1 ++ [A ** B] ++ Delta2) by auto.
        apply element_in_app in H.
        {
          destruct H as [Left | Right].

          - destruct Left as [_ [ _ [l val]]].
            apply app_singleton in val.
            destruct val as [t1 [t2 t3]].
            subst.
            inversion HeqRHEnv. 

          - destruct Right as [ _ [ _ [l val]]].
            subst.

            assert (eq:
                      (A0 # B0 :: l)
                        ++ [A ** B] ++ Delta2 =
                      Delta1 ++ [A ** B] ++ Delta2)
              by auto.
            apply app_inv_tail in eq.
            subst. clear HeqRHEnv.

            (* We reapply TensorR - Coq undoes it *)
            pose proof (TensorR n env1 A env2 B LH1 LH2).
            rename H into LH.
            clear LH1. clear LH2.

            assert (eq1: S n + n0 < S n + S n0) by omega.
            assert (eq2: S n + n0 = S n + n0) by omega.
            assert (RH1':
                      n0; (A0 :: l) ++ [A ** B]
                             ++ Delta2 |- C) by auto.
            assert (RH2':
                      n0; (B0 :: l) ++ [A ** B]
                             ++ Delta2 |- C) by auto.
            apply (IHl (S n + n0) eq1
                       (S n) n0 eq2
                       C (env1 ++ env2) (A0::l) Delta2
                       LH) in RH1'. 
            apply (IHl (S n + n0) eq1
                       (S n) n0 eq2
                       C (env1 ++ env2) (B0::l) Delta2
                       LH) in RH2'.
            destruct RH1' as [z H1].
            destruct RH2' as [z' H2].

            assert (H1':
                      z; ((env1 ++ env2) ++ (A0 :: l))
                           ++ Delta2 |- C)
              by (repeat rewrite <- app_assoc in *;
                  auto).
            apply exchange_subset in H1'.
            destruct H1' as [m1 [_ H1']].
            assert (H2':
                      z'; ((env1 ++ env2) ++ (B0 :: l))
                            ++ Delta2 |- C)
              by (repeat rewrite <- app_assoc in *;
                  auto).
            apply exchange_subset in H2'.
            destruct H2' as [m2 [_ H2']].

            apply (level_depth
                     m1 (((A0 :: l)
                            ++ env1 ++ env2)
                           ++ Delta2) C
                     m2 (((B0 :: l)
                            ++ env1 ++ env2)
                           ++ Delta2) C
             H1') in H2'.

            destruct H2' as [k [Hyp1 Hyp2]].

            assert (Final1:
                      k;
                    A0 :: l ++ env1 ++ env2 ++ Delta2
                    |- C)
              by (repeat rewrite <- app_assoc in *;
                  auto).
            assert (Final2:
                      k;
                    B0 :: l ++ env1 ++ env2 ++ Delta2
                    |- C)
              by (repeat rewrite <- app_assoc in *;
                  auto).

            apply (OplusL k
                          (l ++ env1 ++ env2 ++ Delta2)
                          A0 B0 C Final1) in Final2.

            assert (Final:
                      S k; ((A0 # B0 :: l)
                             ++ (env1 ++ env2))
                             ++ Delta2
                           |- C) 
              by (repeat rewrite <- app_assoc in *;
                  auto).
            apply exchange_subset in Final.

            destruct Final as [m [ _ H]].
            exists m.
            repeat rewrite <- app_assoc in *; auto.
        }


      (* RH is a OplusR1 *)
      + clear IHA1. clear IHA2.
        subst. 

        (* We reapply TensorR - Coq undoes it *)
        pose proof (TensorR n env1 A env2 B LH1 LH2).
        rename H into LH.
        clear LH1. clear LH2.

        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1
                   (S n) n0 eq2
                   A0 (env1 ++ env2) Delta1 Delta2
                   LH) in RH.
        clear eq1. clear eq2. clear LH.
        destruct RH as [z H].

        exists (S z).
        constructor; auto.

        
      (* RH is a OplusR2 *)
      + clear IHA1. clear IHA2.
        subst. 

        (* We reapply TensorR - Coq undoes it *)
        pose proof (TensorR n env1 A env2 B LH1 LH2).
        rename H into LH.
        clear LH1. clear LH2.

        assert (eq1: S n + n0 < S n + S n0) by omega.
        assert (eq2: S n + n0 = S n + n0) by omega.
        apply (IHl (S n + n0) eq1
                   (S n) n0 eq2
                   B0 (env1 ++ env2) Delta1 Delta2
                   LH) in RH.
        clear eq1. clear eq2. clear LH.
        destruct RH as [z H].

        exists (S z).
        apply OplusR2; auto.
        
      (* RH is a Perm *)
      + subst.

          (* We reapply TensorR - Coq undoes it *)
          pose proof (TensorR n env1 A env2 B LH1 LH2).
          rename H into LH.
          clear LH1.
          clear LH2.

          (* We use the IH on l *)
          specialize (IHl  ((S n) + n0)).
          assert (eq1: S n + n0 < S n + S n0)
            by omega.
          specialize (IHl eq1 (S n) n0).
          assert (eq2: S n + n0 = S n + n0)
            by omega.

          specialize (IHl eq2 C (env1 ++ env2)).

          inversion HeqRHEnv as [H].
          apply elements_in_app in H.

          {
            destruct H.

            (* case:                                  *)
            (* In (A1 ** A2) Gamma /\                 *)
            (* (exists l : list formula,              *)
            (*     Gamma = Delta1 ++ [A1 ** A2] ++ l) *)
            - destruct H as [H' H].
              destruct H as [l].
              
              specialize (IHl
                            Delta1
                            (l ++ [A0] ++ [B0] ++ Delta)
                            LH
                         ).
              subst.
              repeat rewrite <- app_assoc in RH.
              specialize (IHl RH).
              destruct IHl.

              repeat rewrite <- app_assoc in HeqRHEnv.
              repeat apply app_inv_head in HeqRHEnv.

              rewrite <- HeqRHEnv.
              exists (S x).
              rewrite app_assoc.
              rewrite app_assoc.
              constructor.
              repeat rewrite <- app_assoc in *.
              assumption.

            (* Other cases *)
            - destruct H.
              
              (* Case:                  *)
              (* A1 ** A2 = B0 /\       *)
              (* Gamma = Delta1 /\      *)
              (* [A0] ++ Delta = Delta2 *)
              + destruct H as [H' H].
                destruct H.
                subst.
                
                specialize (IHl
                              (Delta1 ++ [A0])
                              Delta
                              LH
                           ).
                
                rewrite app_assoc in RH.
                specialize (IHl RH).
                destruct IHl.
                
                simpl in *.
                exists x.
                
                repeat rewrite <- app_assoc in *.

                assumption.

              (* Other Cases *)
              + destruct H.

                (* Case:                     *)
                (* A1 ** A2 = A0 /\          *)
                (* Gamma ++ [B0] = Delta1 /\ *)
                (* Delta = Delta2            *)
                * destruct H as [H' H].
                  destruct H.
                  subst.
                                  
                  specialize (IHl
                                Gamma
                                ([B0] ++ Delta2)
                                LH
                                RH
                             ).
                  
                  simpl in *.
                  destruct IHl.
                  exists x.
                
                  repeat rewrite <- app_assoc in *.

                  assumption.

                (* Case: *)
                (* In (A1 ** A2) Delta /\ *)
                (* (exists l : list formula, *)
                (* Delta = l ++ [A1 ** A2] ++ Delta2) *)
                * destruct H as [H' H].
                  destruct H as [l].
                  specialize (IHl
                                (Gamma ++ [A0] ++ [B0] ++ l)
                                Delta2
                                LH
                             ).
                  subst.
                  repeat rewrite app_assoc in IHl.
                  repeat rewrite app_assoc in RH.
                  specialize (IHl RH).
                  destruct IHl as [x IHl].
                  repeat rewrite <- app_assoc in IHl.

                  rewrite app_assoc in HeqRHEnv.
                  rewrite app_assoc in HeqRHEnv.
                  rewrite app_assoc in HeqRHEnv.
                  apply app_inv_tail in HeqRHEnv.
                  subst.

                  exists (S x).
                  repeat rewrite <- app_assoc.
                  rewrite app_assoc.
                  rewrite app_assoc.
                  constructor.
                  repeat rewrite <- app_assoc in *.
                  assumption.
          }
      }
      
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
  * discriminate. 

  (* LH is OplisL *)
  * intros RH.
    subst. clear IHA1. clear IHA2.
      
    assert (eq1: n + m < S n + m) by omega.
    assert (eq2: n + m = n + m) by omega.
    assert (RH': m; Delta1 ++ [A ** B] ++ Delta2 |- C)
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