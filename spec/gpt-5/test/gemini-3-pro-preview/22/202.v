Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Inductive Any : Type :=
| AInt : Z -> Any
| AList : list Any -> Any
| AStr : string -> Any
| ADict : Any.

Definition int := Z.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AInt z => z = n
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

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [AInt 1; AList [AInt 2; AInt 3]; AInt 4; AList [AInt 5]; AList []; AList [AInt 7; AStr "8"]; AStr "9"; ADict; AInt 1] 
    [1; 4; 1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - simpl. reflexivity.
  - apply fir_cons_nonint.
    + intros n H. simpl in H. contradiction.
    + apply fir_cons_int with (n := 4).
      * simpl. reflexivity.
      * apply fir_cons_nonint.
        -- intros n H. simpl in H. contradiction.
        -- apply fir_cons_nonint.
           ++ intros n H. simpl in H. contradiction.
           ++ apply fir_cons_nonint.
              ** intros n H. simpl in H. contradiction.
              ** apply fir_cons_nonint.
                 --- intros n H. simpl in H. contradiction.
                 --- apply fir_cons_nonint.
                     +++ intros n H. simpl in H. contradiction.
                     +++ apply fir_cons_int with (n := 1).
                         *** simpl. reflexivity.
                         *** apply fir_nil.
Qed.