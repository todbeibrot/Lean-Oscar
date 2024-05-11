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
tuple = (1, true, z, q)

file = "tuple"
save("mrdi-files/$file.mrdi", tuple)
x = load("mrdi-files/$file.mrdi")
println(x)