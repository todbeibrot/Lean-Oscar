using Oscar
using JSON

R, x = QQ["x"]
p = 3 * x^2 - x + 1
s = "teststring"
z = ZZ(42)
q = QQ(1//3)
S5 = symmetric_group(5)
perm = S5(cperm([4,2,3]))
epi = epimorphism_from_free_group(S5) # cant be saved
g_word = preimage(epi, perm) 
matrix = [QQ(1) QQ(2); QQ(3) QQ(4)]
vector = Vector([1, 2, 3])
matrix_inv = inv(matrix)
F = free_group(2)
(f1, f2) = gens(F)
(quot, proj) = quo(F, [f1^2, f2^2, comm(f1, f2)])
rels = relators(quot)

# file = "fp_group_rels"
# save("mrdi-files/$file.mrdi", rels)
# x = load("mrdi-files/$file.mrdi")
# println(x)

# rw system
println("start loading")
GAP.Packages.load("kbmag", install=true)
println(GAP.Packages.locate_package("kbmag"))
f = free_group(2)
(a, b) = gens(f)
rels = [comm(a, b) / a, comm(b, a) / b]
g = quo(f, rels)[1]
g2 = GAP.GapObj(g)
s = GAP.Globals.KBMAGRewritingSystem(g2)
GAP.Globals.SetInfoLevel(GAP.Globals.InfoRWS, 0)
GAP.Globals.MakeConfluent(s)
