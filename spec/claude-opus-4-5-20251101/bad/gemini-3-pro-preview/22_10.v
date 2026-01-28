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

Example test_filter_integers_values : filter_integers_spec [PyInt 1%Z; PyInt (-1)%Z; PyInt 0%Z; PyInt 999%Z] [1%Z; -1%Z; 0%Z; 999%Z].
Proof.
  unfold filter_integers_spec.
  split.
  - simpl.
    reflexivity.
  - intros z.
    split.
    + intros H.
      simpl in H.
      destruct H as [H | [H | [H | [H | H]]]].
      * subst. exists (PyInt 1%Z). split; [simpl; left; reflexivity | reflexivity].
      * subst. exists (PyInt (-1)%Z). split; [simpl; right; left; reflexivity | reflexivity].
      * subst. exists (PyInt 0%Z). split; [simpl; right; right; left; reflexivity | reflexivity].
      * subst. exists (PyInt 999%Z). split; [simpl; right; right; right; left; reflexivity | reflexivity].
      * contradiction.
    + intros [v [H_in H_eq]].
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | H]]]].
      * subst v. injection H_eq as Hz. subst z. simpl. left. reflexivity.
      * subst v. injection H_eq as Hz. subst z. simpl. right. left. reflexivity.
      * subst v. injection H_eq as Hz. subst z. simpl. right. right. left. reflexivity.
      * subst v. injection H_eq as Hz. subst z. simpl. right. right. right. left. reflexivity.
      * contradiction.
Qed.