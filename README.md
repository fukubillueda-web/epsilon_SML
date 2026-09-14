# Langlands’s Second Main Lemma

Lean 4 formalization of Langlands’s Second Main Lemma for local epsilon factors over nonarchimedean local fields.

The exported theorem is [`LanglandsSecondMainLemma.secondMainLemma`](LanglandsSecondMainLemma/Main.lean).

The project uses Lean **4.32.2**, Mathlib **`905b95818eb32af7874a58b427f50c1711a5e96c`**, and the FML release **`7a6cdfa23b5d246919b0d38f6953104756507a42`**.

## Build

```bash
git clone https://github.com/fukubillueda-web/epsilon_SML.git
cd epsilon_SML
git checkout v1.0.0
lake exe cache get
lake build
lake env leanchecker --fresh LanglandsSecondMainLemma.Main
```

The companion mathematical paper is [`references/epsilon_SML.tex`](references/epsilon_SML.tex). See [`SOURCE_MAP.md`](SOURCE_MAP.md) for the paper-to-Lean map.

Author: Fukuhiro Ueda. Apache License 2.0.
