Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition int := Z.

Inductive Any : Type :=
| AnyInt (v : int)
| AnyList (v : list int).

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AnyInt v' => v' = n
  | _ => False
  end.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m H1 H2.
  destruct v; simpl in *; try contradiction.
  subst. reflexivity.
Qed.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Example test_filter_integers : 
  filter_integers_spec 
    [AnyInt 1; AnyList [4]; AnyList [5]; AnyList [7; 8]; AnyInt 8] 
    [1; 8].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - simpl. reflexivity.
  - apply fir_cons_nonint.
    + intros n H. simpl in H. contradiction.
    + apply fir_cons_nonint.
      * intros n H. simpl in H. contradiction.
      * apply fir_cons_nonint.
        -- intros n H. simpl in H. contradiction.
        -- apply fir_cons_int with (n := 8).
           ++ simpl. reflexivity.
           ++ apply fir_nil.
Qed.