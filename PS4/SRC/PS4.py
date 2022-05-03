KB = []
alpha = []
outputLstMi = []


# Doc file input
def Read_CNF(fileName):
    with open(fileName, 'r') as f:
        # Doc alpha va N
        temp = f.readline().split()
        N = int(f.readline())

        # Luu cac literals tu temp vao alpha va xu li viet hoa cac literals
        alpha = []
        for literal in temp:
            if (literal != 'OR' and literal != 'Or' and literal != 'or'):
                if (literal[0] == '-'):
                    alpha.append(literal[0] + literal[1:].capitalize())
                else:
                    alpha.append(literal[0].capitalize() + literal[1:])

        # Rut gon clause va sap xep lai cac literals trong clause        
        alpha = Minimize_Clause(alpha)
        alpha = Sort_Clause(alpha)
        
        # Doc KB
        KB = []
        for i in range(N):
            temp = f.readline().split()
            clause = []

            # Luu cac literals tu temp vao clause va xu li viet hoa cac literals
            for j in range(len(temp)):
                if (temp[j] != 'OR' and temp[j] != 'Or' and temp[j] != 'or'):
                    if (temp[j][0] == '-'):
                        clause.append(temp[j][0] + temp[j][1:].capitalize())
                    else:
                        clause.append(temp[j][0].capitalize() + temp[j][1:])

            # Rut gon clause va sap xep lai cac literals trong clause va them vao KB neu clause khac True
            clause = Minimize_Clause(clause)
            clause = Sort_Clause(clause)
            if (clause != ['1']):
                KB.append(clause)

    return KB, alpha

# Ghi file output
def Write(fileName, outputLstMi, result):
    with open(fileName, 'w') as f:
        for lstM in outputLstMi:
            f.write(str(len(lstM)) + '\n')
            if (len(lstM) == 0):
                break

            for resolvent in lstM:
                if (resolvent == '{}'):
                    f.write('{}')
                else:
                    for i in range(len(resolvent)):
                        if (i != len(resolvent) - 1):
                            f.write(resolvent[i] + ' OR ')
                        else:
                            f.write(resolvent[i])
                        
                f.write('\n')

        if (result):
            f.write('YES')
        else:
            f.write('NO')

# Sap xep lai cac literals trong clause theo thu tu bang chu cai
def Sort_Clause(clause):
    # Dao nguoc literals de dem dau phu dinh ra sau
    for i in range(len(clause)):
        clause[i] = clause[i][::-1]

    # Sap xep cac literals, va dao nguoc lai dang ban dau
    clause.sort()
    for i in range(len(clause)):
        clause[i] = clause[i][::-1]
    
    return clause

# Rut gon literals
def Minimize_Clause(clause):
    i = 0
    j = 0

    # 2 vong lap kiem tra tung cap literals
    while (i < len(clause)):
        j = i + 1

        while (j < len(clause)):
            # Truong hop co hai literals phu dinh nhau, thi tra ve clause True
            if (clause[i] == clause[j][1:] or clause[i][1:] == clause[j]):
                clause = ['1']
                return clause

            # Truong hop co hai literals bang nhau, thi xoa mot literal
            if (clause[i] == clause[j]):
                clause.pop(j)
                j = j - 1

            j = j + 1
        i = i + 1

    return clause

# Phu dinh clause
def Not_CNFClause(clause):
    notClause = []

    # Truong hop clause la True hoac False thi phu dinh lai
    if (clause == ['1']):
        return ['0']
    if (clause == ['0']):
        return ['1']

    # Phu dinh tung literal trong clause
    for literal in clause:
        if (literal[0] == '-'):
            notClause.append([literal[1:]])
        else:
            notClause.append(['-' + literal])

    return notClause

# Kiem tra hai tap hop chua clause set va subset, lieu subset co la con cua set khong
def Is_Subset(set, subset):
    isSubset = True

    # Kiem tra Is_Subset bang cach kiem tra tung clause1 cua subset co nam trong set hay khong
    for clause1 in subset:
        haveClause1InSet = False

        # Kiem tra tung clause2 cua set co bang clause1 hay khong
        for clause2 in set:
            # Neu clause2 bang clause1 thi clause1 co trong set
            if (CNF_Equiv(clause1, clause2)):
                haveClause1InSet = True
                break
        
        # Khong co bat ki clause1 nao thuoc set, tuong duong voi subset khong la tap hop con cua set
        if (not haveClause1InSet):
            isSubset = False
            break

    return isSubset

# Kiem tra 2 clause theo CNF co tuong duong hay khong
def CNF_Equiv(clause1, clause2):
    # Rut gon hai clause
    clause1 = Minimize_Clause(clause1)
    clause2 = Minimize_Clause(clause2)

    # Neu do dai hai clause khac nhau thi 2 clause khong tuong duong
    if (len(clause1) != len(clause2)):
        return False

    # Kiem tra tung literals cua clause1 co trong clause2 hay khong
    for literal in clause1:
        # Neu khong co trong clause2 thi 2 clause khong tuong duong
        if (literal not in clause2):
            return False
    
    return True

# Them 1 clause 'newClause' vao list cac clauses (phep hop cua clauses va newClause)
def Add_Clause(clauses, newClause):
    # Kiem tra newClause co trong clauses hay khong
    for clause in clauses:
        # Neu co clause cua clauses tuong duong voi newClause thi khong them newClause vao clauses
        if (CNF_Equiv(clause, newClause)):
            return clauses

    # Neu khong co clause tuong duong voi newClause thi them newClause vao clauses
    clauses.append(newClause)
    return clauses

# Them list cac clauses moi 'newClauses' vao list cac clauses (phep hop cua clauses va newClauses)
def Add_Clauses(clauses, newClauses):
    # Voi tung clause trong newClauses, goi ham them clause do vao clauses
    for clause in newClauses:
        clauses = Add_Clause(clauses, clause)

    return clauses

# Ham hop giai hai clause Ci va Cj
def PL_Resolve(Ci, Cj):
    resolvents = []

    # 2 vong lap lay tung literals trong Ci va Cj
    for i in range(len(Ci)):
        for j in range(len(Cj)):
            # Kiem tra 2 literals co phu dinh nhau hay khong
            if (Ci[i] == Cj[j][1:] or Ci[i][1:] == Cj[j]):
                # Neu co thi them vao resolvents cac literals trong Ci va Cj (khong them hai literal phu dinh nhau)
                for literal in Ci[:i]:
                    resolvents.append(literal)
                    
                for literal in Ci[i + 1:]:
                    resolvents.append(literal)

                for literal in Cj[:j]:
                    resolvents.append(literal)

                for literal in Cj[j + 1:]:
                    resolvents.append(literal)

                # Rut gon, sap xep va tra ve tham so thu I la clause hop giai cua Ci va Cj, tra ve tham so thu II la co ton tai 2 literals phu dinh nhau
                resolvents = Minimize_Clause(resolvents)
                resolvents = Sort_Clause(resolvents)
                return resolvents, True
    
    # Neu khong co hai literals trong Ci va Cj phu dinh nhau thi lay ca hai clause Ci va Cj; rut gon, sap xep clause ket qua
    # Tra ve tham so thu I la clause ket qua, tra ve tham so thu II la khong ton tai 2 literals phu dinh nhau
    resolvents = Ci.copy()
    resolvents.extend(Cj)
    resolvents = Minimize_Clause(resolvents)
    resolvents = Sort_Clause(resolvents)
    return resolvents, False

# Ham tra ve KB suy ra alpha bang Propositional Logic - Resolution
# Ham luu thong tin vao cau truc outputLstMi de ghi ra file output.txt
# outputLstMi = [ LstM1, LstM2, ..., LstMn ]
# Voi LstMi la tap hop cac resolvents duoc sinh ra trong vong lap thu i, len(LstMi) la tong so resolvents do
def PL_Resolution(KB, alpha, outputLstMi):
    # Tao clauses tu KB va new chua cac clauses duoc suy luan ra
    clauses = KB.copy()
    new = []
    
    # Khi alpha bang True thi KB suy ra alpha la True
    if (alpha == ['1']):
        return True

    # Phu dinh lai alpha va them vao clauses
    notAlpha = Not_CNFClause(alpha)
    clauses = Add_Clauses(clauses, notAlpha)

    print(notAlpha)
    print(clauses)
    # Lap den khi gap hop giai rong hoac khong tao ra hop giai moi
    while 1:
        # Hai vong lap de lay nhung cap clause co the co trong clauses
        for i in range(len(clauses)):
            for j in range(i + 1, len(clauses)):
                # Thuc hien hop giai hai clause clauses[i] va clauses[j]
                resolvents, check = PL_Resolve(clauses[i], clauses[j])

                # Neu hai clauses[i] va clauses[j] khong ton tai hai literals phu dinh nhau, thi tiep tuc tim cap hop giai khac
                if (not check):
                    continue
                
                # Neu hop giai rong thi tao temp gom cac menh de trong clauses va cac resolvents moi trong new va {}
                # Sau do them nhung resolvents moi (chua co trong KB, trong cung vong lap va trong cac vong lap truoc) vao outputLstMi (cac resolvents moi luon nam cuoi list)
                # Tra ve KB suy ra alpha la True
                if (resolvents == []):
                    temp = clauses.copy()
                    temp = Add_Clauses(temp, new)
                    temp.append('{}')
                    outputLstMi.append(temp[len(clauses):])
                    return True

                # Neu hop giai ra clause khac True thi them clause do vao new
                if (resolvents != ['1']):
                    new = Add_Clause(new, resolvents)

        # Kiem tra new co la tap hop con cua clauses hay khong, neu co thi khong the tao hop giai moi
        # Them vao mot LstMi rong va tra ve KB suy ra alpha la False
        if (Is_Subset(clauses, new)):
            outputLstMi.append([])
            return False

        # Tao oldClauses la clauses truoc khi add resolvents moi tu new
        oldClauses = clauses.copy()
        clauses = Add_Clauses(clauses, new)
        
        # Neu clauses sau khi add resolvents dai hon oldClauses
        # thi them nhung resolvents moi (chua co trong KB, trong cung vong lap va trong cac vong lap truoc) vao outputLstMi (cac resolvents moi luon nam cuoi list)
        if (len(oldClauses) != len(clauses)):
            outputLstMi.append(clauses[len(oldClauses):])


# ============================== MAIN FUNCTION ==============================
# Doc du lieu dau vao va luu trong cau truc du lieu thich hop
KB, alpha = Read_CNF('input.txt')

# Goi ham PL_Resolution de thuc thi giai thuat hop giai
checkKBEntailsAlpha = PL_Resolution(KB, alpha, outputLstMi)

# Ghi du lieu dau ra vao tap tin dau ra theo dinh dang hop le
Write('output.txt', outputLstMi, checkKBEntailsAlpha)


for i in range(2, 6):
    KB = []
    alpha = []
    outputLstMi = []
    
    KB, alpha = Read_CNF('input' + str(i) + '.txt')
    checkKBEntailsAlpha = PL_Resolution(KB, alpha, outputLstMi)
    Write('output' + str(i) + '.txt', outputLstMi, checkKBEntailsAlpha)