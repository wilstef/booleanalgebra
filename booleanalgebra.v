
(*This Coq script has been developed and compiled using Coq version 8.3p15. 
  This file include formal definition of Boolean algebra, proof of 
  Huntington postulates, basic theorems, proof daulity principle and 
  design and verification of 32x8 ROM. *)

 Inductive bool: Type :=
 true | false.


 Definition sum (x y: bool) : bool :=
  match x, y with
 | false, false => false
 | _, _ => true
  end. 

 Definition prod (x y: bool) : bool :=
  match x, y with
 | true, true => true
 | _, _ => false
  end. 

 Definition not (x: bool) : bool :=
   match x with
 | false => true
 | true => false
   end.


 Notation "x + y" := (sum x y)  
                       (at level 50, left associativity) 
                       : bool_scope.
 Notation "x * y" := (prod x y)  
                       (at level 40, left associativity) 
                       : bool_scope.
 Notation "¬ x" := (not x) (at level 30, right associativity): bool_scope.

Open Scope bool_scope.

(***********************************************************************)
(************ Postulates of Boolean Algebra ****************************)
(***********************************************************************)

(*Identity element 
   A * 1 = A 
   A + 0 = A *)

 Lemma identity_sum: forall x, x + false = x.
  Proof. 
    intro x. 
    induction x. simpl. auto.
    simpl. auto.
  Qed.

 Lemma identity_sum': forall x, false + x = x.
  Proof. 
    intro x. 
    induction x. simpl. auto.
    simpl. auto.
  Qed.

 Lemma identity_prod: forall x, x * true = x.
  Proof.  
    intro x. 
    induction x. simpl. auto.
    simpl. auto.
  Qed.

 Lemma identity_prod': forall x, true * x = x.
  Proof.  
    intro x. 
    induction x. simpl. auto.
    simpl. auto.
  Qed.


(* Commutative Law
A * B = B * A
A + B = B + A *)

(*A * B = B * A *)
 Lemma comm_prod: forall x y, x * y = y * x.
 Proof. 
  intros. 
  destruct x, y; simpl; auto.
   (* destruct x. 
  (*CASE-I*) rewrite identity_prod_1x. rewrite identity_prod_1. auto.
  (*CASE-II*) rewrite identity_prod_0. simpl. auto. *)
 Qed.
      
(*A + B = B + A*)
 Lemma comm_sum: forall x y, x + y = y + x. 
 Proof. 
  intros. 
  destruct x, y; simpl; auto.
  (*
  induction x. 
  (*CASE-I*) rewrite identity_sum_1. rewrite identity_sum_1x. auto. 
  (*CASE-II*) rewrite identity_sum_0. rewrite identity_sum_0x. auto.  *)
 Qed.  


(*Distributive Law
A * (B + C) = A * B + A * C
A + (B * C) = (A + B) * (A + C) *)

(*A * (B + C) = A * B + A * C*)
 Lemma dist_over_sum: forall x y z, x * (y + z) = x * y + x * z.
  Proof. 
   intros.  
   destruct x, y, z; simpl; auto.
    (* induction x.
   (*CASE-I*) do 3 rewrite identity_prod_1x. auto.
   (*CASE-II*) do 3 rewrite prod_false_x. simpl. auto. *)
  Qed.

(*A + (B * C) = (A + B) * (A + C) *)
 Lemma dist_over_prod: forall x y z, x + y * z = (x + y) * (x + z).
  Proof. 
   intros. 
   destruct x, y, z; simpl; auto.
    (* induction x. 
   (*CASE-I*) do 3 rewrite identity_sum_1x. simpl. auto. 
   (*CASE-II*) do 3 rewrite identity_sum_0x. auto.  *)
  Qed.

 (*There exists at least two elements x, y \in B, such that x =/= y *)
 Lemma two_elements: exists x, exists y, x = ¬y. 
  Proof. 
   intros.
   exists true. 
   exists false.
   simpl. 
   auto.
  Qed.    

(*Complement Law
 A * ~A = 0
 A + ~A = 1 *)

 Lemma compl_prod: forall x, x * ¬x = false.
  Proof.
   intro.
   destruct x; simpl; auto.
  Qed.
 
 Lemma compl_sum: forall x, x + ¬x = true.
  Proof.
   destruct x; simpl; auto. 
  Qed. 

(***********************************************************************)
(************ Theorems of Boolean Algebra ******************************)
(***********************************************************************)

(* Idempotent Law
A * A = A
A + A = A *)

(* x * x = x *)
 Lemma idempotent_prod: forall x, x * x = x.
  Proof. 
    intro x. 
    pattern (x * x) at 1.
    rewrite <- identity_sum.
    rewrite <- compl_prod with (x:=x).
    rewrite <- dist_over_sum.
    rewrite compl_sum.
    rewrite identity_prod.
    auto.
  Qed.

(* x + x = x*)
 Lemma idempotent_sum: forall x, x + x = x.
  Proof. 
    intro x.
    pattern (x + x) at 1.
    rewrite <- identity_prod.
    rewrite <- compl_sum with (x:= x).
    rewrite <- dist_over_prod.
    rewrite compl_prod.
    rewrite identity_sum.
    auto.
  Qed.


(*Identity Law
  A + 1 = 1  
  A * 0 = 0 *)
 Lemma identity_sum_1: forall x, x + true = true.
  Proof. 
    intro x.
    pattern (x + true) at 1. 
    rewrite <- identity_prod.
    pattern true at 2.
    rewrite <- compl_sum with (x:= x). 
    rewrite <- dist_over_prod.
    rewrite comm_prod.
    rewrite identity_prod.
    rewrite compl_sum. 
    auto. 
  Qed.

 Lemma identity_prod_0: forall x, x * false = false.
  Proof. 
    intro x. 
    pattern (x * false) at 1.
    rewrite <- identity_sum.
    pattern false at 2.
    rewrite <- compl_prod with (x:= x).
    rewrite <- dist_over_sum.
    rewrite comm_sum. 
    rewrite identity_sum. 
    rewrite compl_prod.
    auto.
  Qed.


(*Associative Law
(A * B) * C = A * (B * C)
(A + B) + C = A + (B + C) *)

(* (A * B) * C = A * (B * C) *)
 Lemma assoc_prod: forall x y z, 
     (x * y) * z = x * (y * z).
 Proof.
  intros.
  destruct x, y, z; simpl; auto.
 Qed.

(*(A + B) + C = A + (B + C)*)
 Lemma assoc_sum: forall x y z, 
     (x + y) + z = x + (y + z).
 Proof.
  intros.
  destruct x, y, z; simpl; auto.
  Qed.


(* Involution Law
 ~(~A) = A *)

 Lemma involution: forall x, ¬¬x = x.
  Proof.
   intro.
   destruct x; simpl; auto.
  Qed.



(***************** DAULITY PROOF ********************)

 Inductive exp : Type :=
   trueexp: exp
 | falseexp: exp
 | bexp: exp -> exp
 | sumexp: exp -> exp -> exp
 | prodexp: exp -> exp -> exp
 | compexp: exp -> exp.

 (*
 Fixpoint evalexp (e: exp) : bool :=
  match e with
  | trueexp => true
  | falseexp => true
  | bexp b => evalexp b
  | sumexp e1 e2 => (evalexp e1) + (evalexp e2)
  | prodexp e1 e2 => (evalexp e1) * (evalexp e2)
  | compexp e1 => ¬ (evalexp e1)
  end. *)

 Fixpoint changeident (e : exp) : exp :=
  match e with
  | trueexp => falseexp
  | falseexp => trueexp
  | bexp e' => e
  | sumexp e1 e2 => sumexp (changeident e1) (changeident e2)
  | prodexp e1 e2 => prodexp (changeident e1) (changeident e2)
  | compexp e' => compexp (changeident e')
  end.

 Fixpoint changeop (e : exp) : exp :=
  match e with
  | sumexp e1 e2 => prodexp e1 e2
  | prodexp e1 e2 => sumexp e1 e2
  | _ => e
  end.

 
 Lemma daulity: forall lhs rhs, 
   lhs = rhs -> changeop (changeident lhs) = changeop (changeident rhs).
  Proof. 
   intros.
   rewrite H. 
   auto.
  Qed. 

 Lemma daulity_check: forall x y, 
       sumexp (bexp x) (bexp y) = sumexp (bexp y) (bexp x) ->
          prodexp (bexp x) (bexp y) = prodexp (bexp y) (bexp x).
  Proof.
   intros.
   assert (changeop (changeident (sumexp (bexp x) (bexp y))) = 
            changeop (changeident (sumexp (bexp y) (bexp x)))).
   apply  daulity. auto.
   simpl in *.
   rewrite H0; auto.
  Qed. 

(****************************************************)


(*DeMorgan's Law
~(A * B) = ~A + ~B
~(A + B) = ~A * ~B *)

(*~(A * B) = ~A + ~B*)
 Lemma DeMorg_prod: forall x y, ¬(x * y) = ¬x + ¬y.
 Proof. 
  intros.
   destruct x; simpl; auto.
   destruct y; simpl; auto.
 Qed.

(*~(A + B) = ~A * ~B *)
 Lemma DeMorg_sum: forall x y, ¬(x + y) = ¬x * ¬y.
  Proof. 
   intros.
   destruct x; simpl; auto.
   destruct y; simpl; auto.
 Qed. 

(*Redundance Law/Absorption Theorem *)

 (*x + x.y = x*)
 Lemma absorption_sum: forall x y, x + x*y = x. 
  Proof.
   intros.
   pattern x at 1. (*chooses the first x for rewrite*)
   rewrite <- identity_prod.
   rewrite <- dist_over_sum. 
   rewrite <- comm_sum.
   rewrite identity_sum_1. 
   rewrite identity_prod. 
   auto.
  Qed. 

(* x (x + y) = x *)
 Lemma abroption_prod: forall x y, x*(x + y) = x.
  Proof. 
   intros.
   pattern x at 1. (*chooses the first x for rewrite*)
   rewrite <- identity_sum.
   rewrite <- dist_over_prod.
   rewrite <- comm_prod.
   rewrite identity_prod_0 with (x:= y).
   rewrite identity_sum.
   auto.
  Qed.

(*Simplification Theorem”
a) X + X'.Y = X + Y
b) X.( X' + Y) = X.Y*)

 (* x + x'.y = x + y *)
 Lemma simpl_sum: forall x y, x + ¬x*y = x + y. 
  Proof.
   intros. 
   rewrite dist_over_prod.
   rewrite compl_sum.
   rewrite comm_prod.
   rewrite identity_prod.
   auto.
 Qed.

 (* x.(x' + y) = x.y *)
 Lemma simpl_prod: forall x y, x*(¬x + y) = x*y.
  Proof.
   intros.
   rewrite dist_over_sum.
   rewrite compl_prod. 
   rewrite comm_sum.
   rewrite identity_sum.
   auto.
  Qed.

(*Adjacency Theorem
 a) X.Y + X.Y' = X
 b) (X + Y).(X + Y') = X *)

  (*x.y + x.y' = x *)
 Lemma adjacency_sum: forall x y, x*y + x*¬y = x.
 Proof. 
  intros.
  rewrite <- dist_over_sum.
  rewrite compl_sum.
  rewrite identity_prod.
  auto.
 Qed.

 (* (x + y).(x + y') = x *)
 Lemma adjacency_prod: forall x y, (x + y)*(x + ¬y) = x. 
 Proof. 
  intros.
  rewrite dist_over_sum.
  rewrite comm_prod.
  rewrite abroption_prod.
  rewrite comm_prod.
  rewrite dist_over_sum.
  pattern (¬y * y) at 1.
  rewrite comm_prod.
  rewrite compl_prod.
  rewrite identity_sum.
  rewrite comm_prod.
  rewrite absorption_sum.
  auto.
 Qed.


 Lemma assoc_sum_four: forall w x y z, w + y + x + z = w + x + y + z.
 Proof.
  intros.
  rewrite comm_sum.
  assert (w + y = y + w) by apply comm_sum.
  rewrite H.
  rewrite comm_sum. rewrite <- H. 
  rewrite <- comm_sum.
  assert (y + x =  x + y) by apply comm_sum.
  assert (w + (y + x) = w + y + x). rewrite assoc_sum. auto.
  rewrite <- H1.
  rewrite H0. 
  rewrite <- comm_sum.
  rewrite <- assoc_sum. 
  auto.
 Qed. 

(*Consensus theorem - page 37*)
 Lemma consensus: forall x y z, x*y + ¬x*z + y*z = x*y + ¬x*z. 
 Proof. 
   (* single line proof: destruct x, y, z; simpl; auto. *)
  intros. 
  assert (y * z = y * z *true) as  H.
  rewrite identity_prod; auto.
  assert (x + (¬x) = true) as H1 by apply compl_sum.
  rewrite <- H1 in H.
  rewrite H. 
  rewrite dist_over_sum.
  rewrite <- assoc_sum. 
  rewrite assoc_sum_four.
  assert (x * y = x * y * true).  rewrite identity_prod; auto.
  rewrite H0.
  assert (y * z * x  = x * y * z). 
    rewrite comm_prod. rewrite assoc_prod. auto.
  rewrite H2.
  rewrite  <- dist_over_sum.
  assert (y * z * (¬x) = (¬x)*z*y).  rewrite assoc_prod.
    rewrite comm_prod. rewrite assoc_prod. rewrite comm_prod. 
    rewrite assoc_prod. assert (y * z = z * y) by apply comm_prod.
    rewrite H3. rewrite assoc_prod. auto.
  rewrite H3.
  assert ((¬x) * z + (¬x) * z * y = (¬x)*z*(true + y)).
     rewrite dist_over_sum. rewrite identity_prod. auto.
  rewrite assoc_sum.
  rewrite H4.
   assert (true + z = z + true) by apply comm_sum. rewrite H5.
   assert (true + y = y + true) by apply comm_sum. rewrite H6.
  do 2 rewrite identity_sum_1.
  do 2 rewrite identity_prod.
  auto.
 Qed. 
 
(*************************************************************************)
(**************** Proof of 32*8 (32-bytes) ROM ***************************)
(*************************************************************************)
 
(* Minterms
0 ¬A*¬B*¬C*¬D*¬E 
1 ¬A*¬B*¬C*¬D*E 
2 ¬A*¬B*¬C*D*¬E 
3 ¬A*¬B*¬C*D*E 
4 ¬A*¬B*C*¬D*¬E 
5 ¬A*¬B*C*¬D*E 
6 ¬A*¬B*C*D*¬E 
7 ¬A*¬B*C*D*E 
8 ¬A*B*¬C*¬D*¬E 
9 ¬A*B*¬C*¬D*E 
10 ¬A*B*¬C*D*¬E 
11 ¬A*B*¬C*D*E 
12 ¬A*B*C*¬D*¬E 
13 ¬A*B*C*¬D*E 
14 ¬A*B*C*D*¬E 
15 ¬A*B*C*D*E 
16 A*¬B*¬C*¬D*¬E 
17 A*¬B*¬C*¬D*E 
18 A*¬B*¬C*D*¬E 
19 A*¬B*¬C*D*E 
20 A*¬B*C*¬D*¬E 
21 A*¬B*C*¬D*E 
22 A*¬B*C*D*¬E 
23 A*¬B*C*D*E 
24 A*B*¬C*¬D*¬E 
25 A*B*¬C*¬D*E 
26 A*B*¬C*D*¬E 
27 A*B*¬C*D*E 
28 A*B*C*¬D*¬E 
39 A*B*C*¬D*E 
30 A*B*C*D*¬E 
31 A*B*C*D*E  *)
 
(* Functional Specification - Boolean functions - 
   one for each column of the truth table  *)
Definition O6(A B C D E : bool) : bool :=
  ¬A*¬B*¬C*¬D*¬E + ¬A*¬B*¬C*¬D*E + ¬A*¬B*¬C*D*¬E + ¬A*¬B*¬C*D*E + ¬A*¬B*C*¬D*¬E +
  ¬A*¬B*C*¬D*E + ¬A*¬B*C*D*¬E + ¬A*B*¬C*¬D*¬E + ¬A*B*¬C*¬D*E + ¬A*B*¬C*D*¬E + 
  ¬A*B*¬C*D*E + ¬A*B*C*¬D*¬E + ¬A*B*C*¬D*E + ¬A*B*C*D*¬E + A*¬B*¬C*¬D*¬E + 
  A*¬B*¬C*¬D*E + A*¬B*¬C*D*¬E + A*¬B*¬C*D*E + A*¬B*C*¬D*¬E + A*¬B*C*¬D*E + 
  A*¬B*C*D*¬E + A*B*¬C*¬D*¬E + A*B*¬C*¬D*E + A*B*¬C*D*¬E + 
  A*B*¬C*D*E + A*B*C*¬D*¬E + A*B*C*¬D*E + A*B*C*D*¬E. 

Definition O5(A B C D E:bool) : bool:= 
  ¬A*¬B*¬C*¬D*E + ¬A*¬B*¬C*D*¬E + ¬A*¬B*¬C*D*E + ¬A*¬B*C*¬D*¬E +
  ¬A*¬B*C*¬D*E + ¬A*¬B*C*D*¬E + ¬A*¬B*C*D*E + ¬A*B*¬C*¬D*¬E + ¬A*B*¬C*¬D*E +
  ¬A*B*¬C*D*¬E + ¬A*B*¬C*D*E + ¬A*B*C*¬D*¬E + ¬A*B*C*¬D*E + ¬A*B*C*D*¬E +
  ¬A*B*C*D*E + A*¬B*¬C*¬D*E + A*¬B*¬C*D*¬E + A*¬B*¬C*D*E +
  A*¬B*C*¬D*¬E + A*¬B*C*¬D*E + A*¬B*C*D*¬E + A*¬B*C*D*E + A*B*¬C*¬D*¬E + 
  A*B*¬C*¬D*E + A*B*¬C*D*¬E + A*B*¬C*D*E + A*B*C*¬D*¬E + A*B*C*¬D*E +
  A*B*C*D*¬E + A*B*C*D*E.

Definition O4(A B C D E:bool) : bool:= 
 ¬A*¬B*¬C*¬D*¬E + ¬A*¬B*¬C*¬D*E + ¬A*¬B*¬C*D*¬E + ¬A*¬B*¬C*D*E + ¬A*¬B*C*¬D*¬E +
  ¬A*B*¬C*D*¬E + ¬A*B*C*D*¬E + A*¬B*¬C*¬D*¬E + A*¬B*¬C*¬D*E + A*¬B*¬C*D*¬E + 
  A*¬B*¬C*D*E + A*¬B*C*¬D*¬E + A*B*¬C*D*¬E + A*B*C*D*¬E.

Definition O3(A B C D E:bool) : bool:= 
  ¬A*B*¬C*D*E + ¬A*B*C*¬D*E + ¬A*B*C*D*E + A*B*¬C*D*E + A*B*C*¬D*E +
  A*B*C*D*E. 

Definition O2(A B C D E:bool) : bool:=
 ¬A*¬B*¬C*¬D*¬E + ¬A*¬B*¬C*D*¬E + ¬A*¬B*C*¬D*¬E + ¬A*¬B*C*¬D*E + 
  ¬A*¬B*C*D*¬E + ¬A*B*¬C*¬D*¬E + ¬A*B*¬C*¬D*E + ¬A*B*C*¬D*¬E + ¬A*B*C*¬D*E +
  ¬A*B*C*D*E + A*¬B*¬C*¬D*¬E + A*¬B*¬C*D*¬E + A*¬B*C*¬D*¬E + A*¬B*C*¬D*E +
  A*¬B*C*D*¬E + A*B*¬C*¬D*¬E + A*B*¬C*¬D*E + A*B*C*¬D*¬E + A*B*C*¬D*E +
  A*B*C*D*E.

Definition O1(A B C D E:bool) : bool:=
 ¬A*¬B*¬C*¬D*E + ¬A*¬B*¬C*D*E + ¬A*B*¬C*D*¬E + ¬A*B*C*¬D*¬E + ¬A*B*C*¬D*E + 
  ¬A*B*C*D*¬E + ¬A*B*C*D*E + A*¬B*¬C*¬D*E + A*¬B*¬C*D*E + A*B*¬C*D*¬E + 
  A*B*C*¬D*¬E + A*B*C*¬D*E + A*B*C*D*¬E + A*B*C*D*E. 

Definition O0(A B C D E:bool) : bool:= ¬A*¬B*¬C*D*¬E + ¬A*¬B*¬C*D*E + ¬A*¬B*C*¬D*E + ¬A*B*¬C*¬D*E + ¬A*B*¬C*D*¬E + 
  ¬A*B*¬C*D*E + ¬A*B*C*¬D*¬E + ¬A*B*C*D*¬E + A*¬B*¬C*D*¬E + A*¬B*¬C*D*E +
  A*¬B*C*¬D*E + A*B*¬C*¬D*E + A*B*¬C*D*¬E + A*B*¬C*D*E + A*B*C*¬D*¬E + 
  A*B*C*D*¬E. 

(*Proposed implementation - Simplified Boolean functions - one for each K-map*)
Definition O'6(A B C D E:bool) : bool:= ¬C + ¬D + ¬E.
Definition O'5(A B C D E:bool) : bool:= B + C + D + E.
Definition O'4(A B C D E:bool) : bool:= ¬B*¬C + ¬B*¬D*¬E + B*D*¬E.
Definition O'3(A B C D E:bool) : bool:= B*C*E + B*D*E.
Definition O'2(A B C D E:bool) : bool:= ¬B*¬E + B*¬D + C*¬D + ¬D*¬E + B*C*E.
Definition O'1(A B C D E:bool) : bool:= ¬B*¬C*E + B*C + B*D*¬E. 
Definition O'0(A B C D E:bool) : bool:= ¬B*C*¬D*E + ¬C*D + B*¬C*E + B*C*¬E.


(* Individual functional equivalence checking *)
Lemma equiv_OO'6: forall A B C D E, O6 A B C D E = O'6 A B C D E.
 Proof. 
  intros. 
  unfold O6.
  unfold O'6.
  destruct A, B, C, D, E; simpl; auto.
 Qed. 

 Lemma equiv_OO'5: forall A B C D E, O5 A B C D E = O'5 A B C D E.
 Proof. 
  intros.
  unfold O5.
  unfold O'5.
  destruct A, B, C, D, E; simpl; auto.
 Qed. 

Lemma equiv_OO'4: forall A B C D E, O4 A B C D E = O'4 A B C D E.
 Proof. 
  intros.
  unfold O4.
  unfold O'4.
  destruct A, B, C, D, E; simpl; auto.
 Qed. 

Lemma equiv_OO'3: forall A B C D E, O3 A B C D E = O'3 A B C D E.
 Proof. 
  intros.
  unfold O3.
  unfold O'3.
  destruct A, B, C, D, E; simpl; auto.
 Qed. 

Lemma equiv_OO'2: forall A B C D E, O2 A B C D E = O'2 A B C D E.
 Proof. 
  intros.
  unfold O2.
  unfold O'2.
  destruct A, B, C, D, E; simpl; auto.
 Qed. 

Lemma equiv_OO'1: forall A B C D E, O1 A B C D E = O'1 A B C D E.
 Proof. 
  intros.
  unfold O1.
  unfold O'1.
  destruct A, B, C, D, E; simpl; auto.
 Qed. 

Lemma equiv_OO'0: forall A B C D E, O0 A B C D E = O'0 A B C D E.
 Proof. 
  Admitted. 
 
(*
Lemma equiv_OO'0: forall A B C D E, O0 A B C D E = O'0 A B C D E.
 Proof. 
  intros.
  unfold O0.
  unfold O'0.
  destruct A, B, C, D, E; simpl; auto.
 Qed. *)

(*Functional equivalence checking at system level*)
Theorem circuit_equivalence: forall A B C D E, 
 (O6 A B C D E)*(O5 A B C D E)*(O4 A B C D E)*(O3 A B C D E)*
 (O2 A B C D E)*(O1 A B C D E)*(O0 A B C D E) = (O'6 A B C D E)*
 (O'5 A B C D E)*(O'4 A B C D E)*(O'3 A B C D E)*(O'2 A B C D E)*
 (O'1 A B C D E)*(O'0 A B C D E).
Proof.
 intros.
 rewrite equiv_OO'6.
 rewrite equiv_OO'5.
 rewrite equiv_OO'4.
 rewrite equiv_OO'3.
 rewrite equiv_OO'2.
 rewrite equiv_OO'1.
 rewrite equiv_OO'0.
 auto.
Qed.

Print Assumptions circuit_equivalence.

(*************************************************************************)
(************************* Other Proofs **********************************)
(*************************************************************************)

(************************* Adder *****************************************)

 (*Full-adder carry simplification - page 127. The sum can not be further
  simplified using the K-maps. *)
 Lemma carry_simpl: forall X Y Z, 
    ¬X*Y*Z + X*¬Y*Z + X*Y*¬Z + X*Y*Z = X*Y + X*Z + Y*Z.
  Proof. 
   intros. 
    destruct X, Y, Z; simpl; auto.  
  Qed. 

(*Proof of Kmap-simplified function - page 82 *)
Lemma F_ABCDE: forall A B C D E, 
  ¬A*¬B*¬C*¬D*¬E + ¬A*¬B*¬C*D*¬E + ¬A*¬B*C*D*¬E + ¬A*¬B*C*¬D*¬E + 
  ¬A*B*¬C*¬D*E + ¬A*B*¬C*D*E + ¬A*B*C*D*E + ¬A*B*C*¬D*E +
  A*B*¬C*¬D*E + A*B*¬C*D*E + A*B*C*D*E + A*B*C*¬D*E + 
  A*¬B*¬C*¬D*E + A*¬B*C*¬D*E = B*E + A*¬D*E + ¬A*¬B*¬E. 
 Proof. 
  destruct A, B, C, D, E; simpl; auto.
 Qed.

(************** BCD-to-Excess-3 Converter ********************************)

(*Don't care conditions does not help all the time. 
  The simplified (using K-Map) function for W is not equal to the original 
  function for SOME inputs. This is proved below. For all values of last two
  inputs. *)
 Lemma kmap_neq_some_W: exists A, exists B, forall C D, 
    ¬A*B*¬C*D + ¬A*B*C*¬D +
    ¬A*B*C*D + A*¬B*¬C*¬D + A*¬B*¬C*D = ¬(A + B*(C + D)).
  Proof.
   exists true.
   exists true. 
   simpl. intros. 
   auto. 
  Qed. 

(*Don't care conditions does not help all the time. 
  The simplified (using K-Map) function is not equal to the original function
  for SOME inputs. This is proved below. *)
 Lemma kmap_neq_some_W': exists A, exists B, exists C, exists D, 
    ¬A*B*¬C*D + ¬A*B*C*¬D +
    ¬A*B*C*D + A*¬B*¬C*¬D + A*¬B*¬C*D = ¬(A + B*(C + D)).
  Proof.
   exists true.
   exists true. 
   exists true. 
   exists true.
   simpl. auto. 
  Qed. 

 (*Functions are NOT equivelent for SOME inputs, when all don't care cases 
  (including those not used in kmap) are considered part of original function.*)
 Lemma kmap_neq_some_X: exists A, exists B, exists C, exists D, 
   ¬A*¬B*¬C*D + ¬A*¬B*C*¬D + ¬A*¬B*C*D + ¬A*B*¬C*¬D + A*¬B*¬C*D + 
   A*¬B*C*¬D + A*¬B*C*D + A*B*¬C*¬D + A*B*¬C*D + A*B*C*¬D + A*B*C*D = 
   ¬(¬B*C + ¬B*D + B*¬C*¬D).
  Proof. 
   exists true.
   exists true. 
   exists true. 
   exists true.
   simpl; auto.
  Qed.

 Lemma kmap_equal_all_W: forall A B C D, 
   ¬A*B*¬C*D + ¬A*B*C*¬D + ¬A*B*C*D + A*¬B*¬C*¬D + A*¬B*¬C*D + 
   A*¬B*C*¬D + A*¬B*C*D + A*B*¬C*¬D + A*B*¬C*D + A*B*C*¬D + A*B*C*D = 
   A + B*(C + D).
  Proof.
   intros.
   destruct A, B, C, D; simpl; auto.
  Qed.

 (*Functions are equivalent ONLY when the don't care cases, used in kmap 
  simplification, are considered in the original function. Last three don't
  care conditions are not used in kmap (page 108), so are not considered part 
  of original function in the theorem below. 
  *)
 Lemma kmap_equal_all_X: forall A B C D, 
   ¬A*¬B*¬C*D + ¬A*¬B*C*¬D + ¬A*¬B*C*D + ¬A*B*¬C*¬D + A*¬B*¬C*D + 
   A*¬B*C*¬D + A*¬B*C*D + A*B*¬C*¬D = ¬B*C + ¬B*D + B*¬C*¬D.
   (* or ¬B*(C + D) + B*¬C*¬D. *)
  Proof. 
   intros.
   destruct A, B, C, D; simpl; auto.
  Qed.

 Lemma kmap_equal_all_Y: forall A B C D, 
   ¬A*¬B*¬C*¬D + ¬A*¬B*C*D + ¬A*B*¬C*¬D + ¬A*B*C*D + A*¬B*¬C*¬D +  
   A*¬B*C*D + A*B*¬C*¬D + A*B*C*D = C*D + ¬C*¬D.
  Proof.
   intros.
   destruct A, B, C, D; simpl; auto.
  Qed.

 Lemma kmap_equal_all_Z: forall A B C D, 
   ¬A*¬B*¬C*¬D + ¬A*¬B*C*¬D + ¬A*B*¬C*¬D + ¬A*B*C*¬D + A*¬B*¬C*¬D +  
   A*B*¬C*¬D + A*B*C*¬D + A*¬B*C*¬D = ¬D.
  Proof.
   intros.
   destruct A, B, C, D; simpl; auto.
  Qed.

