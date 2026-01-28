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

(* Test case: input = [["apple"; "appaapplebcle"; 2.71828; None; false; "watermelon"; 42; 2.71828; "apple"]], output = [42] *)
Example test_filter_integers_mixed : 
  filter_integers_spec 
    [PyString; PyString; PyFloat; PyOther; PyOther; PyString; PyInt 42%Z; PyFloat; PyString] 
    [42%Z].
Proof.
  unfold filter_integers_spec.
  split.
  - (* Part 1: Verify the implementation returns the expected result *)
    simpl.
    reflexivity.
  - (* Part 2: Verify the logical equivalence *)
    intros z.
    split.
    + (* Direction: In z [42] -> exists v ... *)
      intros H.
      simpl in H. destruct H as [H | H]; [| contradiction].
      subst.
      exists (PyInt 42%Z).
      split.
      * simpl. do 6 right. left. reflexivity.
      * reflexivity.
    + (* Direction: exists v ... -> In z [42] *)
      intros [v [H_in H_eq]].
      subst v.
      simpl in H_in.
      destruct H_in as [H|H]; [discriminate|].
      destruct H as [H|H]; [discriminate|].
      destruct H as [H|H]; [discriminate|].
      destruct H as [H|H]; [discriminate|].
      destruct H as [H|H]; [discriminate|].
      destruct H as [H|H]; [discriminate|].
      destruct H as [H|H].
      * injection H as H_z. subst. left. reflexivity.
      * destruct H as [H|H]; [discriminate|].
        destruct H as [H|H]; [discriminate|].
        contradiction.
Qed.