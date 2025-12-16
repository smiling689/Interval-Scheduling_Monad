# Interval-Scheduling_Monad

This is the repo for the theory assignment in CS2205 PLDI

Class website: [CS 2205, Programming Languages - Design and Implementation, Fall 2025](https://jhc.sjtu.edu.cn/public/courses/CS2205/)

Theory Tasks info: [TopicList_TheoryTask.pdf](https://jhc.sjtu.edu.cn/public/courses/CS2205/TopicList_TheoryTask.pdf)

## Authors

皇甫泊宁，陈奕莱

## Tasks

**Monad 上的证明算法正确性：选择最多的区间使其不相交**

- 算法的输入是右端点递增的一列闭区间，算法使用贪心法求出其中的闭区间，使得这些闭区间 两两不交。

```coq
Definition max_interval (l: list (Z * Z)) (leftmost: Z):
  program (Z * list (Z * Z)) :=
  '(leftmost0, size0, ans0) <- list_iter
    (fun '(l, r) =>
      fun '(leftmost0, size0, ans0) =>
        choice
          (assume (l <= leftmost0);;
           ret (leftmost0, size0, ans0))
          (assume (l > leftmost0);;
           ret (r, size0 + 1, ans0 ++ [(l, r)])))
    l
    (leftmost, 0, []);;
  ret (size0, ans0).
```

该算法中 `leftmost0` 表示现在已经选出的区间中，最右一个的右端点；`size0` 表示目前为止选出的闭区间数量；`ans0` 表示具体选出的闭区间。本题证明中可能要用到子序列 `is_subsequence` 的定义，这可以在附件 `ListLib` 目录 `General` 子目录下的 `IndexedElements.v` 文件中找到。本题的证明中可以使用一个我们提供的最大值最小值库（见附件中 `MaxMinLib`），库中也有一些有用的性质。另外，附件中提供的 `monadlib` 包含了一些 monad 验证的自动化指令。具体信息见附件中根目录 `README` 和子目录 `README`。上述算法定义在 `algorithms` 目录下。详见 `ListAlgTasks.zip`。

- 第二档难度：证明算法的第一项确实是可选区间的最大数量；
- 第三档难度：在上面的基础上证明，算法的第二项输出确实是使得所选区间数量最多的一组方案；
- 第四档难度：证明算法的第二项输出是所有最佳方案中，区间编号字典序最小的方案。