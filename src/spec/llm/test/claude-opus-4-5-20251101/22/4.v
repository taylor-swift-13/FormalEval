Require Import List.
Require Import ZArith.

Import ListNotations.

Inductive PyValue : Type :=
  | PyInt : Z -> PyValue
  | PyFloat : PyValue
  | PyString : PyValue
  | PyDict : PyValue
  | PyList : PyValue
  | PyOther : PyValue.

Definition is_integer (v : PyValue) : bool :=
  match v with
  | PyInt _ => true
  | _ => false
  end.

Definition get_int (v : PyValue) : option Z :=
  match v with
  | PyInt n => Some n
  | _ => None
  end.

Fixpoint filter_integers_impl (values : list PyValue) : list Z :=
  match values with
  | [] => []
  | (PyInt n) :: rest => n :: filter_integers_impl rest
  | _ :: rest => filter_integers_impl rest
  end.

Definition filter_integers_spec (values : list PyValue) (result : list Z) : Prop :=
  result = filter_integers_impl values /\
  (forall z, In z result <-> exists v, In v values /\ v = PyInt z).

Example test_all_integers : filter_integers_spec [PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z] [1%Z; 2%Z; 3%Z; 4%Z; 5%Z].
Proof.
  unfold filter_integers_spec.
  split.
  - simpl. reflexivity.
  - intros z. split.
    + simpl. intros H.
      destruct H as [H | [H | [H | [H | [H | H]]]]].
      * exists (PyInt 1%Z). split. left. reflexivity. rewrite H. reflexivity.
      * exists (PyInt 2%Z). split. right. left. reflexivity. rewrite H. reflexivity.
      * exists (PyInt 3%Z). split. right. right. left. reflexivity. rewrite H. reflexivity.
      * exists (PyInt 4%Z). split. right. right. right. left. reflexivity. rewrite H. reflexivity.
      * exists (PyInt 5%Z). split. right. right. right. right. left. reflexivity. rewrite H. reflexivity.
      * contradiction.
    + intros [v [Hv Heq]].
      simpl in Hv. simpl.
      destruct Hv as [Hv | [Hv | [Hv | [Hv | [Hv | Hv]]]]].
      * rewrite <- Hv in Heq. injection Heq as Heq. left. exact Heq.
      * rewrite <- Hv in Heq. injection Heq as Heq. right. left. exact Heq.
      * rewrite <- Hv in Heq. injection Heq as Heq. right. right. left. exact Heq.
      * rewrite <- Hv in Heq. injection Heq as Heq. right. right. right. left. exact Heq.
      * rewrite <- Hv in Heq. injection Heq as Heq. right. right. right. right. left. exact Heq.
      * contradiction.
Qed.