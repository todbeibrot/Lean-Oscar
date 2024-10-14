# Lean-Oscar
An interface between [Lean](https://lean-lang.org/) and [Oscar](https://docs.oscar-system.org/stable/).
To see what is already working take a look at [test.lean](./test.lean).
I added the [write up of my master's thesis](./masterthesis.pdf) for more detailed information.
Feedback and questions are always welcome!

## How to install

You need to [install Lean](https://leanprover-community.github.io/get_started.html) and [install Oscar](https://www.oscar-system.org/install/)

Clone the repository:
```bash
git clone https://github.com/todbeibrot/Lean-Oscar.git
```

Navigate to the project directory:
```bash
cd Lean-Oscar
```

Build the project:
```bash
lean exe cache get
```

and
```bash
lake build
```

Then, open test.lean and see if everything compiles.
