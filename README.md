# survey-family-unification
Code associated with [1]

Guide to files:
`symmetry_break.wl` -> a small Mathematica package dedicated to using LieArt 2.0 [2] to compute non-Abelian and Abelian symmetry breakings as defined in [1]
`survey.nb` -> a Mathematica notebook exhibiting the derivation of all quantitative results found in [1] (using `symmetry_break.wl`)
`hists.ipynb` -> a Python Jupyer notebook importing `.txt` data files outputted by `survey.nb` (found in `./data`) and producing the figures found in [1] (saved in `./hists`)

References:
[1] A Survey of Family Unification Models with Bifundamental Matter; T. Kephart and E. Sheridan ([arXiv](https://arxiv.org/abs/2206.13309))
[2] LieART 2.0 – A Mathematica application for Lie Algebras and Representation Theory; R. Feger, T. Kephart, R. Saskowski ([CPC](https://www.sciencedirect.com/science/article/abs/pii/S0010465520302290?via%3Dihub))
