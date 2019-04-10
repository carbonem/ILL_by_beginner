From Coq Require Import Lists.List.
Import ListNotations.

(* Formulas *)
Inductive formula : Type :=
| One
| Atom (a : nat)
| Tensor (A B : formula)
| Lolli (A B : formula)
| Oplus (A B : formula)
| With (A B : formula).

Notation "A ** B" := (Tensor A B) (at level 50).
Notation "A -o B" := (Lolli A B) (at level 50). 
Notation "A # B" := (Oplus A B) (at level 50). 
Notation "A & B" := (With A B) (at level 50). 

(* Rules *)
Inductive mill: nat -> (list formula)  -> formula -> Prop
  :=
  | OneL n Gamma A (H: mill n Gamma A):
      mill (S n) (One :: Gamma) A
  | OneR n : mill n [] One
  | Ax n A : mill n [A] A
  | TensorL n env A B C
            (H : mill n (A :: B :: env) C) :
      mill (S n) (A ** B ::  env)  C
  | TensorR n env1 A env2 B
            (H1 : mill n env1 A)
            (H2 : mill n env2 B) :
      mill (S n) (env1 ++ env2) (A ** B)
  | LolliL n env1 A env2 B C
           (H1 : mill n env1 A)
           (H2 : mill n (B :: env2) C) :
      mill (S n) ( A -o B :: env1 ++ env2) C
  | LolliR n env A B
           (H : mill n (A :: env) B) :
      mill (S n) env (A -o B)
  | WithL1 n Gamma A B C
           (H : mill n (A::Gamma) C) :
      mill (S n) (A & B :: Gamma) C
  | WithL2 n Gamma A B C
           (H : mill n (B::Gamma) C) :
      mill (S n) (A & B :: Gamma) C
  | WithR n Gamma A B
          (H1 : mill n Gamma A)
          (H2 : mill n Gamma B) : 
      mill (S n) Gamma (A & B)
  | OplusL n Gamma A B C
           (H1 : mill n (A::Gamma) C)
           (H2 : mill n (B::Gamma) C) :
      mill (S n) (A # B :: Gamma) C           
  | OplusR1 n Gamma A B
           (H : mill n Gamma A) :
      mill (S n) Gamma (A # B)
  | OplusR2 n Gamma A B
           (H : mill n Gamma B) :
      mill (S n) Gamma (A # B)
  | Perm n Gamma Delta A B C
         (H : mill n (Gamma ++ [A] ++ [B] ++ Delta) C) :
      mill (S n) (Gamma ++ [B] ++ [A] ++ Delta) C.


Notation "n ; Gamma |- A" := (mill n Gamma A)
                                 (at level 30).
