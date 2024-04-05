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

file = "matrix_inv"
save("mrdi-files/$file.mrdi", matrix_inv)
x = load("mrdi-files/$file.mrdi")
println(x)
