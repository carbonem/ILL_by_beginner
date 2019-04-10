From Coq Require Import Lists.List.
From Coq Require Import omega.Omega.
Import ListNotations.

(* Useful Lemmas on lists *)
Lemma app_singleton : forall {X : Type} (A B : X) l1 l2,
    [A] = l1 ++ [B] ++ l2 -> l1 = [] /\ l2 = [] /\ A = B.
Proof.
  intros. 
  destruct l1.
  - simpl in *. 
    injection H.
    intros.
    subst.
    auto.
  - injection H.
    intros.
    destruct l1.
    + simpl in *.
      discriminate.
    + simpl in *.
      discriminate.
Qed.

Proposition same_length :
  forall {X : Type} (l1 l2 l3 l4 : list X),
    length l1 = length l3 ->
    l1 ++ l2 = l3 ++ l4 ->
    l1 = l3.
Proof.
  intros X l1.
  induction l1.
  - simpl in *.
    intros.
    assert (0 = (length l3) -> length l3 = 0) by omega.
    apply H1 in H.
    apply length_zero_iff_nil in H.
    auto.
  - intros.
    simpl in *.
    destruct l3.
    * simpl in *.
      discriminate.
    * simpl in *.
      injection H.
      intros.
      specialize (IHl1 l2 l3 l4 H1).
      injection H0.
      intros.
      specialize (IHl1 H2).
      subst.
      auto.
Qed. 
      

Lemma element_in_app :
  forall {X : Type} (l1 l2 l3 l4 : list X) A,
    l1 ++ l2 = l3 ++ [A] ++ l4
    ->
    (In A l1 /\ length l3 < length l1 /\
     exists l, l1 = l3 ++ [A] ++ l)
    \/ 
    (In A l2 /\ length l1 <= length l3 /\
     exists l,  l2 = l ++ [A] ++ l4).
Proof.
  intros X l1 l2 l3 l4 A H.
  assert (either:
            length l1 = length l3 \/
            length l3 < length l1 \/
            length l1 < length l3)
         by omega.
  destruct  either.

  (* length l1 = length l3 *)
  - inversion H.
    apply (same_length l1 l2 l3 (A::l4) H0) in H2.
    subst.
    apply app_inv_head in H.
    subst.
    right.
    split.
    + simpl.
      left.
      auto.
    + split.
      * omega.
      * exists [].
        reflexivity.

      
  (* remaining cases *) 
  - destruct H0.

    (* length l1 > length l3, hence A is in l1 *)
    + left.
      generalize dependent l4.
      generalize dependent l3.
      generalize dependent l2.
      {
        induction l1.
        -  intros.
           simpl in *.
           omega.
        - intros.
          destruct l3.
          * simpl in *.
            inversion H.
            subst.
            split.
            + left; auto.
            + split. omega. exists l1. auto.
          * simpl in *.
            inversion H.
            subst.
            apply lt_S_n in H0.
            specialize (IHl1 l2 l3 H0 l4 H3).
            destruct IHl1.
            split.
            + right; auto.
            + {
                split.
                - omega.
                - destruct H2 as [eq1 [l eq2]].
                  subst.
                  injection H.
                  intros Hyp1.
                  rewrite <- app_assoc in Hyp1.
                  apply app_inv_head in Hyp1.
                  inversion Hyp1.
                  subst.
                  assert (eq: (x :: (l3 ++ A :: l)) ++ l2 =
                              (x :: l3 ++ A :: l) ++ l2)
                    by auto.
                  apply app_inv_tail in eq.
                  exists l.
                  auto.
              }
      }
      
    (* length l3 > length l1, hence A is in l2 *)
    + right.
      generalize dependent l4.
      generalize dependent l3.
      generalize dependent l2.
      {
        induction l1.
        - intros.
          simpl in *.
          subst.
          split.
          * apply in_or_app.
            right.
            simpl.
            left.
            auto.
          * split.
            omega.
            exists l3.
            auto.
            
        - destruct l3.
          * intros.
            simpl in *.
            omega.
          * intros.
            simpl in *.
            injection H.
            intros.
            subst.
            apply lt_S_n in H0.
            specialize (IHl1 l2 l3 H0 l4 H1 ).
            destruct IHl1.
            split.
            + auto.
            + split.
              omega.
              destruct H3.
              destruct H4.
              exists x0.
              subst.
              auto.
      }
Qed. 

Lemma element_in_app_head :
  forall {X : Type} (l2 l3 l4 : list X) A B,
    A :: l2 = l3 ++ [B] ++ l4
    ->
    l3 = [] /\ A=B /\ l2 = l4
    \/ 
    exists l,  l2 = l ++ [B] ++ l4.
Proof.
  intros.
  assert (H': [A] ++ l2 = l3 ++ [B] ++ l4) by auto.
  apply element_in_app in H'.
  destruct H' as [Left | Right].
  - destruct Left as [ _ [ _ [l H']]].
    apply app_singleton in H'.
    destruct H' as [t1 [t2 t3]].
    left.
    subst.
    inversion H.
    subst.
    auto.
  - destruct Right as [_ [ _ [ l H']]].
    subst.
    right.
    assert (eq: (A :: l) ++ [B] ++ l4 = l3 ++ [B] ++ l4)
      by auto.
    apply app_inv_tail in eq.
    subst.
    exists l; auto.
Qed. 

Lemma elements_in_app :
  forall {X : Type} (l1 l2 l3 l4 : list X) A B C,
    l1 ++ [A] ++ [B] ++ l2 = l3 ++ [C] ++ l4
    ->
    (In C l1 /\ exists l, l1 = l3 ++ [C] ++ l)
    \/ 
    (C = A /\ l1 = l3 /\ [B] ++ l2 = l4)
    \/
    (C = B /\ l1 ++ [A] = l3 /\ l2 = l4)
    \/
    (In C l2 /\ exists l, l2 = l ++ [C] ++ l4).
Proof.
  intros.

  assert (either:
            length l3 < length l1 \/
            length l1 = length l3 \/
            length l1 + 1 = length l3 \/
            length l1 + 2 <= length l3)
    by omega.
  
  destruct  either.

  (* Case in which |l3| < |l1| *)
  - left. 
    generalize dependent l4.
    generalize dependent l3.
    generalize dependent l2.
    {
      induction l1.
      -  intros.
         simpl in *.
         omega.
      - intros.
        destruct l3.
        * simpl in *.
          injection H.
          intros.
          subst.
          split.
          + left. auto.
          + exists l1. auto.
        * simpl in *.
          injection H.
          intros.
          subst.
          apply lt_S_n in H0.
          specialize (IHl1 l2 l3 H0 l4 H1 ).
          destruct IHl1.
          split.
          + right. auto.
          + destruct H3.
            exists x0.
            subst.
            auto.
    }

    
  (* remaining cases *)
  - { destruct H0.
      
      (* Case in which |l1| = |l3| *)
      - inversion H.
        apply (same_length l1 (A::B::l2) l3 (C::l4) H0) in H2.
        subst.
        apply app_inv_head in H.
        simpl in *.
        injection H.
        intros.
        subst. 
        right. left.
        split; auto.
        
      (* remaining cases *)
      - { destruct H0.

          (* Case in whcih |l1| + 1 = |l3| *)
          - inversion H.
            assert (length (l1 ++ [A]) = length l3).
            { rewrite app_length.
              simpl.
              auto.
            }
            right. right. left.
            rewrite app_assoc in H.
            apply
              (same_length (l1 ++ [A]) (B::l2) l3 (C::l4) H1)
              in H.
            subst.
            rewrite <- app_assoc in H2.
            apply app_inv_head in H2.
            simpl in *.
            injection H2.
            intros.
            subst.
            split; auto.

          (* Case in whcih |l1| + 2 <= |l3| *)
          - right. right. right.
            rewrite app_assoc in H.
            rewrite app_assoc in H.
            apply
              (element_in_app
                 ((l1 ++ [A]) ++ [B])
                 l2
                 l3
                 l4
                 C) in H.
            destruct H.
            + destruct H.
              destruct H1. 
              repeat rewrite app_length in H1.
              simpl in *.
              omega.
              
            + destruct H.
              destruct H1.
              split.
              * auto.
              * destruct H2.
                exists x.
                auto.
        }
    }
Qed. 



Lemma tail_list :
  forall {X : Type} (l : list X),
    l = []
    \/
    exists l' A,  l = l' ++ [A].
Proof.
  induction l.
  - left. auto.
  - right.
    destruct IHl.
    * subst.
      exists [].
      exists a.
      auto.
    * destruct H.
      destruct H.
      subst.
      exists (a :: x).
      exists x0.
      auto.
Qed.

