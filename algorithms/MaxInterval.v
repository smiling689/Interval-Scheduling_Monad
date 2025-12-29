Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import ListLib.General.IndexedElements.
Require Import ListLib.General.Forall.
Require Import ListLib.General.Length.
Require Import ListLib.Base.Positional.
From RecordUpdate Require Import RecordUpdate.
From MonadLib.SetMonad Require Import SetBasic SetHoare FixpointLib.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope Z.

(* ============================================= *)
(* 基础定义：区间、可行解、右端点有序等         *)
(* ============================================= *)

Definition interval := (Z * Z)%type.

Definition left (it: interval): Z := fst it.
Definition right (it: interval): Z := snd it.

(* 右端点非递减（输入序列按右端点递增） *)
Fixpoint right_increasing (l: list interval): Prop :=
  match l with
  | nil => True
  | (l1, r1) :: rest =>
      Forall (fun it => r1 <= right it) rest /\ right_increasing rest
  end.

(* 从给定右端点开始，后续区间严格不相交 *)
Fixpoint non_overlap_from (leftmost: Z) (ans: list interval): Prop :=
  match ans with
  | nil => True
  | (l, r) :: ans' => leftmost < l /\ non_overlap_from r ans'
  end.

Definition valid_solution (l: list interval) (leftmost: Z) (ans: list interval): Prop :=
  is_subsequence ans l /\ non_overlap_from leftmost ans.

(* --------------------------------------------- *)
(* 子序列相关的基础引理                           *)
(* --------------------------------------------- *)

(* 左侧连接上新元素，原序列的子序列依然是新序列的子序列 *)
Lemma is_subsequence_cons_r {A: Type}:
  forall (a: A) l1 l2,
    is_subsequence l1 l2 ->
    is_subsequence l1 (a :: l2).
Proof.
  intros a l1 l2 Hsub.
  destruct l1 as [| x xs]; simpl.
  - auto.
  - left; exact Hsub.
Qed.

(* 空序列的子序列为空 *)
Lemma is_subsequence_nil_inv {A: Type}:
  forall (l: list A),
    is_subsequence l nil ->
    l = nil.
Proof.
  intros l Hsub.
  destruct l; simpl in Hsub; auto.
  contradiction.
Qed.

(* 子序列去掉首元素，仍是子序列 *)
Lemma is_subsequence_drop_head {A: Type}:
  forall (x: A) (xs: list A) (l: list A),
    is_subsequence (x :: xs) l ->
    is_subsequence xs l.
Proof.
  induction l as [| a l IH]; simpl; intros; try contradiction.
  destruct H as [Hskip | [Heq Htail]].
  - apply is_subsequence_cons_r.
    apply IH; exact Hskip.
  - apply is_subsequence_cons_r; exact Htail.
Qed.

(* 子序列与原序列同时去掉首元素，剩余保持子序列关系 *)
Lemma is_subsequence_tail {A: Type}:
  forall (x: A) (xs: list A) (a: A) (l: list A),
    is_subsequence (x :: xs) (a :: l) ->
    is_subsequence xs l.
Proof.
  intros x xs a l Hsub.
  simpl in Hsub.
  destruct Hsub as [Hskip | [Heq Htail]].
  - apply is_subsequence_drop_head in Hskip; exact Hskip.
  - exact Htail.
Qed.

(* 子序列首元素与原序列首元素不同，则去除原序列首元素保持子序列关系 *)
Lemma is_subsequence_cons_skip {A: Type}:
  forall (x: A) (xs: list A) (a: A) (l: list A),
    x <> a ->
    is_subsequence (x :: xs) (a :: l) ->
    is_subsequence (x :: xs) l.
Proof.
  intros x xs a l Hneq Hsub.
  simpl in Hsub.
  destruct Hsub as [Hskip | [Heq _]]; auto.
  contradiction.
Qed.

(* 子序列元素出现在原序列 *)
Lemma is_subsequence_in {A: Type}:
  forall x xs (l: list A),
    is_subsequence (x :: xs) l ->
    In x l.
Proof.
  (* Print In. *)
  induction l as [| a l IH]; simpl; intros; try contradiction.
  destruct H as [Hskip | [Heq Htail]].
  - right; apply IH; exact Hskip.
  - subst; left; reflexivity.
Qed.

(* --------------------------------------------- *)
(* 右端点有序的常用性质                           *)
(* --------------------------------------------- *)

Lemma right_increasing_tail:
  forall a l,
    right_increasing (a :: l) ->
    right_increasing l.
Proof.
  intros a l Hinc.
  destruct a as [la ra]; simpl in Hinc.
  tauto.
Qed.

(* 任意可接在已选区间前的区间，右端点小于等于已选区间内任意区间右端点 *)
Lemma right_increasing_head_le:
  forall a l b,
    right_increasing (a :: l) ->
    In b l ->
    right a <= right b.
Proof.
  destruct a as [la ra].
  simpl; intros.
  destruct H as [Hfor _].
  pose proof (proj1 (Forall_forall (fun it => ra <= right it) l) Hfor) as Hall.
  apply Hall; exact H0.
Qed.

(* 任意可接在已选区间前的区间，右端点小于等于总区间的首区间右端点 *)
Lemma right_increasing_head_le_subseq:
  forall l1 r1 rest l2 r2 ans',
    right_increasing ((l1, r1) :: rest) ->
    is_subsequence ((l2, r2) :: ans') ((l1, r1) :: rest) ->
    r1 <= r2.
Proof.
  intros l1 r1 rest l2 r2 ans' Hinc Hsub.
  pose proof is_subsequence_in _ _ _ Hsub as Hin.
  simpl in Hin.
  destruct Hin as [Heq | Hin].
  - inversion Heq. reflexivity.
  - pose proof (right_increasing_head_le (l1, r1) rest (l2, r2) Hinc Hin) as Hle.
    simpl in Hle; exact Hle.
Qed.

(* --------------------------------------------- *)
(* 不相交性质的简单推论                           *)
(* --------------------------------------------- *)

(* 更弱的左侧最大右端点区间仍然保持不相交 *)
Lemma non_overlap_from_weaken_leftmost:
  forall leftmost leftmost' ans,
    leftmost' <= leftmost ->
    non_overlap_from leftmost ans ->
    non_overlap_from leftmost' ans.
Proof.
  intros leftmost leftmost' ans Hle Hno.
  destruct ans as [| [l r] ans']; simpl in *; auto.
  destruct Hno as [Hlt Hrest].
  split; [lia | exact Hrest].
Qed.

(* 已选区间与原序列首区间相交，则不选该首区间 *)
Lemma valid_solution_skip_head:
  forall leftmost l1 r1 rest ans,
    leftmost >= l1 ->
    valid_solution ((l1, r1) :: rest) leftmost ans ->
    valid_solution rest leftmost ans.
Proof.
  intros leftmost l1 r1 rest ans Hge [Hsub Hno].
  destruct ans as [| [l0 r0] ans']; simpl in *.
  - split.
    + destruct rest; simpl; auto.
    + simpl; auto.
  - destruct Hno as [Hlt Htail].
    assert (Hneq: (l0, r0) <> (l1, r1)) by (intro Heq; inversion Heq; lia).
    apply is_subsequence_cons_skip in Hsub; [| exact Hneq].
    split; auto.
    simpl; tauto.
Qed.

(* ============================================= *)
(* 贪心选择的纯函数版本与关键性质                 *)
(* ============================================= *)

(* 贪心选择：l1 > leftmost 就选 *)
Fixpoint greedy_iter_list (l: list interval) (leftmost: Z) (ans: list interval): list interval :=
  match l with
  | nil => ans
  | (l1, r1) :: rest =>
      if Z_le_dec l1 leftmost
      then greedy_iter_list rest leftmost ans
      else greedy_iter_list rest r1 (ans ++ [(l1, r1)])
  end.

Definition greedy_list (l: list interval) (leftmost: Z): list interval :=
  greedy_iter_list l leftmost [].

Definition greedy_size (l: list interval) (leftmost: Z): Z :=
  Zlength (greedy_list l leftmost).

(* 连续选择只会在尾部追加 *)
Lemma greedy_iter_list_prefix:
  forall l leftmost ans,
    greedy_iter_list l leftmost ans = ans ++ greedy_iter_list l leftmost [].
Proof.
  induction l as [| [l1 r1] rest IH]; simpl; intros.
  - now rewrite app_nil_r.
  - destruct (Z_le_dec l1 leftmost) as [Hle | Hgt].
    + rewrite IH; reflexivity.
    + rewrite IH.
      rewrite (IH r1 [(l1, r1)]).
      rewrite app_assoc; reflexivity.
Qed.

(* 贪心选择单步性质 *)
Lemma greedy_list_cons:
  forall l1 r1 rest leftmost,
    greedy_list ((l1, r1) :: rest) leftmost =
    if Z_le_dec l1 leftmost
    then greedy_list rest leftmost
    else (l1, r1) :: greedy_list rest r1.
Proof.
  intros l1 r1 rest leftmost.
  unfold greedy_list; simpl.
  destruct (Z_le_dec l1 leftmost) as [Hle | Hgt]; auto.
  rewrite greedy_iter_list_prefix; simpl.
  reflexivity.
Qed.

(* 贪心结果一定是原列表的子序列 *)
Lemma greedy_list_subsequence:
  forall l leftmost,
    is_subsequence (greedy_list l leftmost) l.
Proof.
  induction l as [| [l1 r1] rest IH]; simpl; intros.
  - auto.
  - rewrite greedy_list_cons.
    destruct (Z_le_dec l1 leftmost) as [Hle | Hgt].
    + apply is_subsequence_cons_r; apply IH.
    + right; split; [reflexivity | apply IH].
Qed.

(* 贪心结果满足严格不相交 *)
Lemma greedy_list_non_overlap:
  forall l leftmost,
    non_overlap_from leftmost (greedy_list l leftmost).
Proof.
  induction l as [| [l1 r1] rest IH]; simpl; intros.
  - auto.
  - rewrite greedy_list_cons.
    destruct (Z_le_dec l1 leftmost) as [Hle | Hgt].
    + apply IH.
    + simpl; split; [lia | apply IH].
Qed.

Lemma greedy_list_valid:
  forall l leftmost,
    valid_solution l leftmost (greedy_list l leftmost).
Proof.
  intros l leftmost.
  split.
  - apply greedy_list_subsequence.
  - apply greedy_list_non_overlap.
Qed.

(* 贪心长度是最大可行长度（第二档核心结论） *)
Lemma greedy_list_optimal_size:
  forall l leftmost,
    right_increasing l ->
    forall ans,
      valid_solution l leftmost ans ->
      Zlength ans <= greedy_size l leftmost.
Proof.
  induction l as [| [l1 r1] rest IH]; intros leftmost Hinc ans Hvalid.
  - destruct Hvalid as [Hsub _].
    apply is_subsequence_nil_inv in Hsub; subst.
    unfold greedy_size, Zlength; simpl; lia.
  - unfold greedy_size.
    rewrite greedy_list_cons.
    destruct (Z_le_dec l1 leftmost) as [Hle | Hgt].
    + apply valid_solution_skip_head in Hvalid; [| lia].
      apply IH.
      * apply right_increasing_tail in Hinc; exact Hinc.
      * exact Hvalid.
    + destruct ans as [| [l0 r0] ans'].
      * unfold Zlength; simpl; lia.
      * destruct Hvalid as [Hsub Hno].
        (* 贪心选择区间右端点更小 *)
        pose proof right_increasing_head_le_subseq l1 r1 rest l0 r0 ans' Hinc Hsub as Hle_r.
        (* 去除首元素，后续答案仍在子序列中 *)
        pose proof (is_subsequence_tail _ _ _ _ Hsub) as Hsub_tail.
        destruct Hno as [_ Htail].
        (* r1 相比 r0 更弱，因此仍不交 *)
        pose proof (non_overlap_from_weaken_leftmost _ _ _ Hle_r Htail) as Hno_tail.
        pose proof IH r1 (right_increasing_tail _ _ Hinc) ans' (conj Hsub_tail Hno_tail)
          as Hbound.
        unfold greedy_size in Hbound.
        rewrite Zlength_cons.
        rewrite Zlength_cons.
        lia.
Qed.


(* ============================================= *)
(* 字典序最小性：索引序列与字典序比较             *)
(* ============================================= *)

Fixpoint lex_lt (l1 l2: list Z): Prop :=
  match l1, l2 with
  | nil, nil => False
  | nil, _ :: _ => True
  | _ :: _, nil => False
  | x1 :: t1, x2 :: t2 =>
      x1 < x2 \/ x1 = x2 /\ lex_lt t1 t2
  end.

Definition lex_le (l1 l2: list Z): Prop :=
  l1 = l2 \/ lex_lt l1 l2.

(* 字典序自反性 *)
Lemma lex_le_refl:
  forall l, lex_le l l.
Proof.
  intros; left; reflexivity.
Qed.

(* 首元素比较字典序 *)
Lemma lex_lt_cons_lt:
  forall x1 x2 t1 t2,
    x1 < x2 ->
    lex_lt (x1 :: t1) (x2 :: t2).
Proof.
  simpl; intros; auto.
Qed.

(* 去除首元素比较字典序 *)
Lemma lex_lt_cons_eq:
  forall x t1 t2,
    lex_lt t1 t2 ->
    lex_lt (x :: t1) (x :: t2).
Proof.
  simpl; intros; auto.
Qed.

(* 可取等版本 *)
Lemma lex_le_cons_eq:
  forall x t1 t2,
    lex_le t1 t2 ->
    lex_le (x :: t1) (x :: t2).
Proof.
  intros x t1 t2 [Heq | Hlt].
  - left; subst; reflexivity.
  - right; apply lex_lt_cons_eq; exact Hlt.
Qed.

(* 索引全+1保序 *)
Lemma lex_lt_map_add1:
  forall l1 l2,
    lex_lt l1 l2 ->
    lex_lt (map (fun z => z + 1) l1) (map (fun z => z + 1) l2).
Proof.
  induction l1 as [| x1 t1 IH]; destruct l2 as [| x2 t2]; simpl; intros; try tauto.
  destruct H as [Hlt | [Heq Hlt]].
  - left; lia.
  - subst x2.
    apply lex_lt_cons_eq.
    apply IH; exact Hlt.
Qed.

(* 可取等版本 *)
Lemma lex_le_map_add1:
  forall l1 l2,
    lex_le l1 l2 ->
    lex_le (map (fun z => z + 1) l1) (map (fun z => z + 1) l2).
Proof.
  intros l1 l2 [Heq | Hlt].
  - left; subst; reflexivity.
  - right; apply lex_lt_map_add1; exact Hlt.
Qed.

(* ============================================= *)
(* 待补全：贪心索引序列相关性质 *)
(* ============================================= *)

Lemma sincr_tail:
  forall a l,
    sincr (a :: l) ->
    sincr l.
Proof.
  destruct l; simpl; intros; auto.
  destruct H as [_ Hrest]; exact Hrest.
Qed.

Lemma greedy_size_cons:
  forall l1 r1 rest leftmost,
    greedy_size ((l1, r1) :: rest) leftmost =
    if Z_le_dec l1  leftmost
    then greedy_size rest leftmost
    else greedy_size rest r1 + 1.
Proof.
  intros l1 r1 rest leftmost.
  unfold greedy_size.
  rewrite greedy_list_cons.
  destruct (Z_le_dec l1 leftmost) as [Hle | Hgt].
  - reflexivity.
  - rewrite Zlength_cons; lia.
Qed.

Lemma greedy_size_nonneg:
  forall l leftmost,
    0 <= greedy_size l leftmost.
Proof.
  intros; unfold greedy_size; apply Zlength_nonneg.
Qed.

Lemma map_sub_add1_id:
  forall il,
    map (fun z => z - 1 + 1) il = il.
Proof.
  induction il as [| z il IH]; simpl; [reflexivity |].
  f_equal; [lia | exact IH].
Qed.

(* ============================================= *)
(* 程序语义与贪心结果的连接                        *)
(* ============================================= *)

Definition state := (Z * Z * list interval)%type.

Definition max_interval_body (it: interval) (st: state): program state :=
  let '(l, r) := it in
  let '(leftmost0, size0, ans0) := st in
  choice
    (assume (l <= leftmost0);;
     ret (leftmost0, size0, ans0))
    (assume (l > leftmost0);;
     ret (r, size0 + 1, ans0 ++ [(l, r)])).

(* 约定：leftmost 小于可选区间的左端点，l 的右端点非递减 *)
Definition max_interval (l: list (Z * Z)) (leftmost: Z):
  program (Z * list (Z * Z)) :=
  '(leftmost0, size0, ans0) <- list_iter
                                 max_interval_body
                                l
                                (leftmost, 0, []);;
  ret (size0, ans0).

Definition greedy_step (it: interval) (st: state): state :=
  let '(l, r) := it in
  let '(leftmost0, size0, ans0) := st in
  if Z_le_dec l leftmost0
  then (leftmost0, size0, ans0)
  else (r, size0 + 1, ans0 ++ [(l, r)]).

Fixpoint greedy_iter_state (l: list interval) (st: state): state :=
  match l with
  | nil => st
  | it :: rest => greedy_iter_state rest (greedy_step it st)
  end.

Definition greedy_state (l: list interval) (leftmost: Z): state :=
  greedy_iter_state l (leftmost, 0, []).

Definition greedy_ans (l: list interval) (leftmost: Z): list interval :=
  let '(_, _, ans0) := greedy_state l leftmost in ans0.

Definition greedy_size_state (l: list interval) (leftmost: Z): Z :=
  let '(_, size0, _) := greedy_state l leftmost in size0.

(* 迭代末尾单步展开 *)
Lemma greedy_iter_state_snoc:
  forall l st it,
    greedy_iter_state (l ++ [it]) st =
    greedy_step it (greedy_iter_state l st).
Proof.
  induction l as [| x l IH]; simpl; intros.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

(* 纯函数与状态迭代在 ans 上一致 *)
Lemma greedy_iter_state_ans:
  forall l leftmost size ans,
    let '(_, _, ans') := greedy_iter_state l (leftmost, size, ans) in
    ans' = greedy_iter_list l leftmost ans.
Proof.
  induction l as [| [l1 r1] rest IH]; simpl; intros.
  - reflexivity.
  - destruct (Z_le_dec l1 leftmost) as [Hle | Hgt]; apply IH.
Qed.

(* size 与 ans 长度保持同步 *)
Lemma greedy_step_size_inv:
  forall it leftmost0 size0 ans0,
    size0 = Zlength ans0 ->
    let '(_, size1, ans1) := greedy_step it (leftmost0, size0, ans0) in
    size1 = Zlength ans1.
Proof.
  intros [l r] leftmost0 size0 ans0 Hsize.
  unfold greedy_step; simpl.
  destruct (Z_le_dec l leftmost0) as [Hle | Hgt].
  - exact Hsize.
  - rewrite Zlength_app_cons.
    lia.
Qed.

Lemma greedy_iter_state_size:
  forall l leftmost size ans,
    size = Zlength ans ->
    let '(_, size', ans') := greedy_iter_state l (leftmost, size, ans) in
    size' = Zlength ans'.
Proof.
  induction l as [| it rest IH]; simpl; intros.
  - exact H.
  - destruct (greedy_step it (leftmost, size, ans)) as [[leftmost1 size1] ans1] eqn:Hst1.
    specialize (greedy_step_size_inv it leftmost size ans H) as Hstep.
    rewrite Hst1 in Hstep; simpl in Hstep.
    specialize (IH leftmost1 size1 ans1 Hstep) as Hrest.
    exact Hrest.
Qed.

Lemma greedy_state_result:
  forall l leftmost,
    let '(_, size0, ans0) := greedy_state l leftmost in
    size0 = greedy_size l leftmost /\ ans0 = greedy_list l leftmost.
Proof.
  intros l leftmost.
  unfold greedy_state.
  destruct (greedy_iter_state l (leftmost, 0, [])) as [[leftmost0 size0] ans0] eqn:Hst.
  
  pose proof (greedy_iter_state_ans l leftmost 0 []) as Hans.
  rewrite Hst in Hans; simpl in Hans.
  
  split.
  - assert (Hinit: 0 = Zlength (@nil interval)) by (simpl; reflexivity).
    pose proof (greedy_iter_state_size l leftmost 0 [] Hinit) as Hsize.
    rewrite Hst in Hsize; simpl in Hsize.
    
    unfold greedy_size, greedy_list.
    rewrite Hans in Hsize; exact Hsize.
  - unfold greedy_list; exact Hans.
Qed.

Lemma Hoare_max_interval_body:
  forall it st,
    Hoare (max_interval_body it st)
          (fun st' => st' = greedy_step it st).
Proof.
  intros [l r] st.
  destruct st as [[leftmost0 size0] ans0].
  unfold max_interval_body, greedy_step; simpl.
  apply Hoare_choice.
  - eapply Hoare_assume_bind; intro Hle.
    apply Hoare_ret; intros; subst.
    destruct (Z_le_dec l leftmost0) as [Hle' | Hgt']; [reflexivity | contradiction].
  - eapply Hoare_assume_bind; intro Hgt.
    apply Hoare_ret; intros; subst.
    destruct (Z_le_dec l leftmost0) as [Hle' | Hgt']; [contradiction | reflexivity].
Qed.

Lemma Hoare_list_iter_state:
  forall l leftmost,
    Hoare (list_iter max_interval_body l (leftmost, 0, []))
          (fun st => st = greedy_state l leftmost).
Proof.
  intros l leftmost.
  eapply Hoare_list_iter with
    (P := fun prefix st => st = greedy_iter_state prefix (leftmost, 0, [])).
  - intros b l' a Hb.
    subst b.
    eapply Hoare_conseq.
    + intros st' Hst'.
      rewrite greedy_iter_state_snoc.
      exact Hst'.
    + apply Hoare_max_interval_body.
  - simpl; reflexivity.
Qed.

Lemma Hoare_max_interval_state:
  forall l leftmost,
    Hoare (max_interval l leftmost)
          (fun '(size, ans) =>
             size = greedy_size l leftmost /\
             ans = greedy_list l leftmost).
Proof.
  intros l leftmost.
  eapply Hoare_bind.
  - apply Hoare_list_iter_state.
  - intros st Hst.
    destruct st as [[leftmost0 size0] ans0].
    simpl in Hst.
    apply Hoare_ret.
    simpl.
    pose proof greedy_state_result l leftmost as Hres.
    rewrite <- Hst in Hres; simpl in Hres.
    exact Hres.
Qed.

(* 第二档：最大数量正确性 *)
Theorem max_interval_opt_size:
  forall l leftmost,
    right_increasing l ->
    Hoare (max_interval l leftmost)
          (fun '(size, ans) =>
             forall ans',
               valid_solution l leftmost ans' ->
               Zlength ans' <= size).
Proof.
  intros l leftmost Hinc.
  apply (@Hoare_conseq
          ((Z * list (Z * Z))%type)
          (max_interval l leftmost)
          (fun '(size, ans) =>
              size = greedy_size l leftmost /\ ans = greedy_list l leftmost)
          (fun '(size, ans) =>
              forall ans',
                valid_solution l leftmost ans' ->
              Zlength ans' <= size)).
- intros [size ans] [Hsize Hans] ans' Hvalid.
  subst size ans.
  apply greedy_list_optimal_size; auto.
- apply Hoare_max_interval_state.
Qed.

(* 第三档：最大数量的具体方案正确性 *)
Theorem max_interval_opt_solution:
  forall l leftmost,
    right_increasing l ->
    Hoare (max_interval l leftmost)
          (fun '(size, ans) =>
             valid_solution l leftmost ans /\
             size = Zlength ans /\
             (forall ans',
               valid_solution l leftmost ans' ->
               Zlength ans' <= size)).
Proof.
  intros l leftmost Hinc.
  apply (@Hoare_conseq
           ((Z * list (Z * Z))%type)
           (max_interval l leftmost)
           (fun '(size, ans) =>
              size = greedy_size l leftmost /\ ans = greedy_list l leftmost)
           (fun '(size, ans) =>
              valid_solution l leftmost ans /\
             size = Zlength ans /\
             (forall ans',
               valid_solution l leftmost ans' ->
               Zlength ans' <= size))).
  - intros [size ans] [Hsize Hans].
    subst size ans.
    split.
    + apply greedy_list_valid.
    + split.
      * unfold greedy_size; reflexivity.
      * apply greedy_list_optimal_size; auto.
  - apply Hoare_max_interval_state.
Qed.

(* 第四档：最优方案中字典序最小的区间编号 *)
Theorem max_interval_opt_lexicographic:
  forall l leftmost,
    right_increasing l ->
    Hoare (max_interval l leftmost)
          (fun '(size, ans) =>
             exists il,
               sincr il /\
               is_indexed_elements l il ans /\
                size = Zlength ans /\
                (forall ans' il',
                  valid_solution l leftmost ans' ->
                  sincr il' ->
                  is_indexed_elements l il' ans' ->
                  Zlength ans' = size ->
                  lex_le il il')).
Admitted.