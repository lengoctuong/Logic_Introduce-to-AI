KB = []
alpha = []

# Doc file input
def Read_CNF(fileName):
    with open(fileName, 'r') as f:
        # Doc alpha va N
        alpha = f.readline().split()
        N = int(f.readline())

        # Xu li viet hoa literal trong alpha
        temp = ''
        if (alpha[0][0] == '-'):
            temp = alpha[0][0] + alpha[0][1:].capitalize()
        else:
            temp = alpha[0][0].capitalize() + alpha[0][1:]
        alpha = [temp]
        
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

            # Rut gon literals va them vao KB neu literals khac True
            clause = Minimize_Clause(clause)
            if (clause != ['1']):
                KB.append(clause)

    return KB, alpha

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

                # Rut gon va tra ve clause hop giai cua Ci va Cj
                return Minimize_Clause(resolvents)
    
    # Neu khong co hai literals trong Ci va Cj phu dinh nhau thi lay ca hai clause Ci va Cj, rut gon clause ket qua ve tra ve
    resolvents = Ci.copy()
    resolvents.extend(Cj)
    return Minimize_Clause(resolvents)

# Ham tra ve KB suy ra alpha bang Propositional Logic - Resolution
def PL_Resolution(KB, alpha):
    # Tao clauses tu KB va new chua cac clauses duoc suy luan ra
    clauses = KB.copy()
    new = []

    # Phu dinh lai alpha va them vao clauses
    if (alpha[0][0] == '-'):
        clauses.append([alpha[0][1:]])
    else:
        clauses.append(['-' + alpha[0]])
    
    # Lap den khi gap hop giai rong hoac khong tao ra hop giai moi
    while 1:
        # Hai vong lap de lay nhung cap clause co the co trong clauses
        for i in range(len(clauses)):
            for j in range(i + 1, len(clauses)):
                # Thu hien hop giai hai clause do
                resolvents = PL_Resolve(clauses[i], clauses[j])
                
                # Neu hop giai rong thi KB suy ra alpha la True, neu hop giai ra clause khac True thi them clause do vao new
                if (resolvents == []):
                    return True
                if (resolvents != ['1']):
                    new = Add_Clause(new, resolvents)

        # Kiem tra new co la tap hop con cua clauses hay khong, neu co thi khong the tao hop giai moi, nen KB suy ra alpha la False
        if (Is_Subset(clauses, new)):
            return False

        # Neu van co hop giai moi thi them new vao clauses
        clauses = Add_Clauses(clauses, new)

# xu li alpha la cau co nhieu symbol
# xu li ghi file output.txt
# xu li sap xep cac literals theo thu tu
# viet report

KB, alpha = Read_CNF('input.txt')
print(KB)
print(alpha)
print(PL_Resolution(KB, alpha))
# ====================================================================================================


# ====================================================================================================
# S =  [ ]  # Store clause set S in list form

# """
# Read the clauses in the clause set file and store them in the S list
#     -Each clause is also stored as a list
#     -Disjunctively split
#     -For example: ~p v ~q v r The storage format is ['~p','~q','r']
# """ 
# def  readClauseSet ( filePath ) : 
#     global S
#     for line in  open ( filePath , mode =  'r' , encoding =  'utf-8' ) : 
#         line = line. replace ( '' ,  '' ) . strip ( )
#         line = line.Split ( 'v' ) 
#         S . append (line )


# """
# -If it is positive text, return its negative text
# -If it is negative text, return its positive text
# """ 
# def  opposite ( clause ) : 
#     if  '~'  in clause : 
#         return clause . replace ( '~' ,  '' ) 
#     else : 
#         return  '~'  + clause


# """
# Boil down
# """ 
# def resolution ( ) : 
#     global S
#     End =  False 
#     while  True : 
#         if End :  break
#         father = S . POP ( ) 
#         for i in father [ : ] : 
#             if End :  break 
#             for mother in S [ : ] : 
#                 if End :  break 
#                 j =  list ( filter (  lambda X : x ==opposite ( i ) , mother ) ) 
#                 if j ==  [ ] : 
#                     continue 
#                 else : 
#                     print ( '\nParent clause: '  +  ' v ' . join ( father )  +  ' and '  +  ' v ' . join ( mother ) ) 
#                     father . remove ( i ) 
#                     mother . remove ( j [ 0 ] )
#                     if ( father ==  [ ]  and mother ==  [ ] ) : 
#                         print ( 'Resolution: NIL' ) 
#                         end =  True 
#                     elif father ==  [ ] : 
#                         print ( 'Resolution:'  +  ' v ' . join ( mother ) ) 
#                     elif mother ==  [ ] : 
#                         print ( 'Resolution:'  +  ' v ' . join ( mother) ) 
#                     else : 
#                         print ( 'Resolution:'  +  ' v ' . join ( father )  +  ' v '  +  ' v ' . join ( mother ) )
                   

# def  ui ( ) : 
#     print ( '----' ) 
#     print ( '-------- Propositional logic resolution reasoning system --------' ) 
#     print ( '----' )


# def  main ( ) : 
#     readClauseSet ( 'input.txt' ) 
#     ui ( ) 
#     resolution ( )


# if __name__ ==  ' __main__ ' : 
#     main ( )
# ====================================================================================================