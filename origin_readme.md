# 整数列表算法形式化验证大作业

这是课程的大作业文档，旨在让学生使用Coq定理证明器完成三个经典动态规划或贪心算法的正确性证明。

## 项目结构

```
.
├── algorithms/           # 算法证明目标（学生需完成的部分）
│
├── monadlib/             # Monad程序库
│   ├── StateRelMonad/    # 状态关系Monad
│   ├── SetMonad/         # 集合Monad（主要使用）
│   └── MonadErr/         # 带错误处理的Monad
│
├── ListLib/              # 列表操作库
|
├── extremumlib/          # 最值库
│   ├── MaxMin.v          # 最大最小值定义
│   ├── Nat/              # 自然数最值
│   └── Z/                # 整数最值
│
├── sets/                 # 集合论库
└── fixedpoints/          # 不动点理论库
```

## 核心库介绍

### MonadLib - Monad程序库

提供基于状态关系Monad的程序语义框架，用于自然地描述和验证算法。

**主要操作符：**
- `ret a` - 返回值a，不改变状态
- `x <- m;; f x` - 顺序组合（bind）
- `assume P` / `assume!! P` - 条件假设
- `choice m1 m2` - 非确定性选择
- `while cond body` - 循环结构
- `list_iter l f` - 列表迭代
- `update'` - 状态更新

**Hoare逻辑：**
```coq
Hoare P c Q  (* 前条件P，程序c，后条件Q *)
```

**常用策略：**
- `hoare_bind H` - 使用H作为中间断言
- `hoare_step` - 单步推进
- `hoare_auto` - 自动推进

### ListLib - 列表库

提供列表操作的常用性质，如`In`、`nth`、`length`等操作的引理。

### ExtremumLib - 最值库

提供最值相关定义和性质。

**主要定义：**
- `min_object_of_subset` - 子集中的最小元素

## 环境要求

- **Coq 8.20.1**
- 依赖库已包含在项目中

## 编译说明

直接在根目录下
```bash
make depend
make
```

## 提示

1. 仔细阅读各库的源代码，理解提供的定义和引理
2. 善用`Search`命令查找可用的引理
3. 使用`Print`查看定义的展开形式
4. 循环不变式是证明的关键，需要仔细设计

---
