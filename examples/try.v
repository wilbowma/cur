Definition plus_n_O : forall n : nat, n = n + 0 :=
fun n : nat =>
nat_ind (fun n0 : nat => n0 = n0 + 0) eq_refl
  (fun (n0 : nat) (IHn : n0 = n0 + 0) => f_equal S IHn) n.

Definition plus_n_Sm : forall n m : nat, S (n + m) = n + S m :=
fun n m : nat =>
nat_ind (fun n0 : nat => S (n0 + m) = n0 + S m) eq_refl
  (fun (n0 : nat) (IHn : S (n0 + m) = n0 + S m) => f_equal S IHn) n.
    
Definition plus_comm : forall n m : nat, n + m = m + n := 
fun n m : nat =>
nat_ind (fun n0 : nat => n0 + m = m + n0) (plus_n_O m)
  (fun (y : nat) (H : y + m = m + y) =>
   eq_ind (S (m + y)) (fun n0 : nat => S (y + m) = n0) 
     (f_equal S H) (m + S y) (plus_n_Sm m y)) n.

Fixpoint ft (l: nat): Type :=
  match l with
  | O => unit
  | S n => (bool * ft n) % type
  end.

Fixpoint concat {n1 n2} : ft n1 -> ft n2 -> ft (n1 + n2) :=
  match n1 as n1_PAT return ft n1_PAT -> ft n2 -> ft (n1_PAT + n2) with
  | O => fun _ l2 => l2
  | S n => fun l1 =>
    match l1 with
    | (b, l1') => fun l2 => (b, concat l1' l2)
    end
  end.

(* Question 1: Ideally, I could have the following syntactic sugar, can you do that?

Fixpoint concat {n1 n2} (l1: ft n1) (l2: ft n2) : ft (n1 + n2) :=
  match n1 with
  | O => l2
  | S n => 
    match l1 with
    | (b, l1') => (b, concat l1' l2)
    end
  end.

*)

Definition concat' {n1 n2} (l1: ft n1) (l2: ft n2): ft (n1 + n2) :=
  eq_rect_r ft (concat l2 l1) (plus_comm _ _).

Goal (@concat' 1 1 (true, tt) (false, tt)) = (false, (true, tt)).
Proof.
  unfold concat'.
  simpl (@concat 1 1 (false, tt) (true, tt)).
  cbv delta [plus_comm plus_n_Sm plus_n_O nat_ind eq_ind].
  simpl.
  (* Question 2: In this step, Coq does a large number of computation to compute a proof term to eq_refl. This is super inefficient for any function application of eq_rect_r. Is there a possible way to customize the method of reducing a term in your system? For example, when you see a eq_rect_r, directly computes two types (which should be equivalent) and check if they are convertible. If yes, tag new type on the term directly. *)
  reflexivity.
Qed.
