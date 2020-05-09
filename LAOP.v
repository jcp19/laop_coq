Require Import Nat.
Require Import Coq.setoid_ring.Ring_theory.
Set Implicit Arguments.
Print LoadPath.

Inductive matrix (X:Type) : nat -> nat -> Type :=
  | one : forall (x:X), matrix X 1 1
  | join : forall {e} {a} {b}, matrix X e a -> matrix X e b -> matrix X e (a+b)
  | fork : forall {e} {a} {b}, matrix X a e -> matrix X b e -> matrix X (a+b) e.

Check one 1.

Check join (one 1) (one 2).

(* TODO: define alternative notation for the contructors *)

Fixpoint tr (X:Type){a:nat} {b:nat} (m : matrix X a b) : matrix X b a :=
  match m with
  | one x => one x
  | join m1 m2 => fork (tr m1) (tr m2)
  | fork m1 m2 => join (tr m1) (tr m2)
  end.

Theorem tr_tr: forall (X:Type)(a b:nat) (m: matrix X a b), tr (tr m) = m.
Proof.
  intros X a b. induction m.
  - reflexivity.
  - simpl. rewrite IHm1. rewrite IHm2. reflexivity.
  - simpl. rewrite IHm1. rewrite IHm2. reflexivity.
Qed.

Print Coq.setoid_ring.Ring_theory.semi_ring_theory.
Definition nat_semiring := @semi_ring_theory nat 0 1 add mul eq.

Fixpoint abideJF (X:Type){a b:nat} (m : matrix X a b) : matrix X a b :=
  match m with
  | one e => one e
  | join (fork a c) (fork b d) => fork (join (abideJF a) (abideJF b)) (join (abideJF c) (abideJF d))
  | fork a b => fork (abideJF a) (abideJF b)
  | @join _ e c d i j => @join X e c d (@abideJF X e c i) (@abideJF X e d j)
  end.

Fixpoint zipWithMatrix (X Y Z:Type){a:nat} {b:nat} (f: X -> Y -> Z) (m : matrix X a b) (n: matrix Y a b):
  matrix Z a b :=
  match m,n with
  | one a, one b => one (f a b)
  | join a b, join c d => join (zipWithMatrix f a c) (zipWithMatrix f b d)
  | fork a b, fork c d => fork (zipWithMatrix f a c) (zipWithMatrix f b d)
  | 
  end.

(*
zipWithM f (One a) (One b)           = One (f a b)
zipWithM f (Join a b) (Join c d)     = Join (zipWithM f a c) (zipWithM f b d)
zipWithM f (Fork a b) (Fork c d)     = Fork (zipWithM f a c) (zipWithM f b d)
zipWithM f x@(Fork _ _) y@(Join _ _) = zipWithM f x (abideJF y)
zipWithM f x@(Join _ _) y@(Fork _ _) = zipWithM f (abideJF x) y
*)

Fixpoint msum {X:Type} {r0 rI: X}{radd rmul : X -> X -> X} {req : X -> X -> Prop}
{a b c:nat} (t: @semi_ring_theory X r0 rI radd rmul req)
(m: matrix X a b) (n: matrix X a b) : matrix X a b.
  (* TODO: define with zipWithMatrix *)

(** Matrix Composition **)
Fixpoint comp {X:Type} {r0 rI: X}{radd rmul : X -> X -> X} {req : X -> X -> Prop}
{a b c:nat} (t: @semi_ring_theory X r0 rI radd rmul req)
(m: matrix X a b) (n: matrix X b c) : matrix X a c :=
  match m, n with
  | one a, one b => one (rmul a b)
  | join a b, fork c d => 
  | a, b => a
  end.

(*
comp (One a) (One b)       = One (a * b)
comp (Join a b) (Fork c d) = comp a c + comp b d         -- Divide-and-conquer law
comp (Fork a b) c          = Fork (comp a c) (comp b c) -- Fork fusion law
comp c (Join a b)          = Join (comp c a) (comp c b)  -- Join fusion law
*)