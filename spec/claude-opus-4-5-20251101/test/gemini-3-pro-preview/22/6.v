Require Import List.
Require Import ZArith.

Import ListNotations.
Open Scope Z_scope.

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

(* Test case: input = [true; false; None; 0; -10; "test"; []; {}; 3.14], output = [0; -10] *)
Example test_filter_integers_mixed : 
  filter_integers_spec 
    [PyOther; PyOther; PyOther; PyInt 0; PyInt (-10); PyString; PyList; PyDict; PyFloat] 
    [0; -10].
Proof.
  unfold filter_integers_spec.
  split.
  - (* Part 1: Verify the implementation returns the expected result *)
    simpl.
    reflexivity.
  - (* Part 2: Verify the logical equivalence *)
    intros z.
    split.
    + (* Direction: In z result -> exists v in values... *)
      intros H.
      simpl in H.
      destruct H as [H0 | [Hn10 | H_false]].
      * (* z = 0 *)
        subst z.
        exists (PyInt 0).
        split.
        -- simpl. do 3 right. left. reflexivity.
        -- reflexivity.
      * (* z = -10 *)
        subst z.
        exists (PyInt (-10)).
        split.
        -- simpl. do 4 right. left. reflexivity.
        -- reflexivity.
      * (* False *)
        contradiction.
    + (* Direction: exists v in values... -> In z result *)
      intros [v [H_in H_eq]].
      subst v.
      simpl in H_in.
      destruct H_in as [H | H_in]; [discriminate H |]. (* true *)
      destruct H_in as [H | H_in]; [discriminate H |]. (* false *)
      destruct H_in as [H | H_in]; [discriminate H |]. (* None *)
      destruct H_in as [H | H_in]. (* 0 *)
      * injection H as Hz. subst z. simpl. left. reflexivity.
      * destruct H_in as [H | H_in]. (* -10 *)
        -- injection H as Hz. subst z. simpl. right. left. reflexivity.
        -- destruct H_in as [H | H_in]; [discriminate H |]. (* "test" *)
           destruct H_in as [H | H_in]; [discriminate H |]. (* [] *)
           destruct H_in as [H | H_in]; [discriminate H |]. (* {} *)
           destruct H_in as [H | H_in]; [discriminate H |]. (* 3.14 *)
           contradiction.
Qed.