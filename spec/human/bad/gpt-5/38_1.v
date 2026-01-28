Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Definition get_char (s : string) (n : nat) : ascii :=
  match String.get n s with
  | Some c => c
  | None => " "%char
  end.

Definition problem_38_pre (input : string) : Prop := True.

Definition problem_38_spec (input output : string) : Prop :=
  String.length input = String.length output /\
  (
    let n := ((String.length input / 3) * 3 - 1)%nat in
    let L := String.length input in
    forall i, (i < L)%nat ->
      let out_char := get_char output i in
      (
        ( (i <= n)%nat ->
          (
            ( ((i + 1) mod 3 = 1%nat) /\ (out_char = get_char input (i + 2)) ) \/
            ( (((i + 1) mod 3 = 2%nat) \/ ((i + 1) mod 3 = 0%nat)) /\ (out_char = get_char input (i - 1)) )
          )
        ) /\
        ( (~(i <= n)%nat) ->
          (
            out_char = get_char input i
          )
        )
      )
  ).

Example problem_38_test :
  problem_38_spec "uzfplzjfzcltmdly" "fuzzplzjftcllmdy".
Proof.
  unfold problem_38_spec.
  simpl.
  split; [reflexivity|].
  cbn.
  intros i Hi.
  destruct i as [|i]; cbn.
  - split.
    + intros _. left. split; [reflexivity|]. cbn. reflexivity.
    + intros H. exfalso. lia.
  - destruct i as [|i]; cbn.
    + split.
      * intros _. right. split.
        { left. reflexivity. }
        cbn. reflexivity.
      * intros H. exfalso. lia.
    + destruct i as [|i]; cbn.
      * split.
        { intros _. right. split.
          { right. reflexivity. }
          cbn. reflexivity.
        }
        { intros H. exfalso. lia. }
      * destruct i as [|i]; cbn.
        { split.
          { intros _. left. split; [reflexivity|]. cbn. reflexivity. }
          { intros H. exfalso. lia. }
        }
        { destruct i as [|i]; cbn.
          { split.
            { intros _. right. split.
              { left. reflexivity. }
              cbn. reflexivity.
            }
            { intros H. exfalso. lia. }
          }
          { destruct i as [|i]; cbn.
            { split.
              { intros _. right. split.
                { right. reflexivity. }
                cbn. reflexivity.
              }
              { intros H. exfalso. lia. }
            }
            { destruct i as [|i]; cbn.
              { split.
                { intros _. left. split; [reflexivity|]. cbn. reflexivity. }
                { intros H. exfalso. lia. }
              }
              { destruct i as [|i]; cbn.
                { split.
                  { intros _. right. split.
                    { left. reflexivity. }
                    cbn. reflexivity.
                  }
                  { intros H. exfalso. lia. }
                }
                { destruct i as [|i]; cbn.
                  { split.
                    { intros _. right. split.
                      { right. reflexivity. }
                      cbn. reflexivity.
                    }
                    { intros H. exfalso. lia. }
                  }
                  { destruct i as [|i]; cbn.
                    { split.
                      { intros _. left. split; [reflexivity|]. cbn. reflexivity. }
                      { intros H. exfalso. lia. }
                    }
                    { destruct i as [|i]; cbn.
                      { split.
                        { intros _. right. split.
                          { left. reflexivity. }
                          cbn. reflexivity.
                        }
                        { intros H. exfalso. lia. }
                      }
                      { destruct i as [|i]; cbn.
                        { split.
                          { intros _. right. split.
                            { right. reflexivity. }
                            cbn. reflexivity.
                          }
                          { intros H. exfalso. lia. }
                        }
                        { destruct i as [|i]; cbn.
                          { split.
                            { intros _. left. split; [reflexivity|]. cbn. reflexivity. }
                            { intros H. exfalso. lia. }
                          }
                          { destruct i as [|i]; cbn.
                            { split.
                              { intros _. right. split.
                                { left. reflexivity. }
                                cbn. reflexivity.
                              }
                              { intros H. exfalso. lia. }
                            }
                            { destruct i as [|i]; cbn.
                              { split.
                                { intros _. right. split.
                                  { right. reflexivity. }
                                  cbn. reflexivity.
                                }
                                { intros H. exfalso. lia. }
                              }
                              { destruct i as [|i]; cbn.
                                { split.
                                  { intros Hle. exfalso. lia. }
                                  { intros _. cbn. reflexivity. }
                                }
                                { exfalso. lia. }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
Qed.