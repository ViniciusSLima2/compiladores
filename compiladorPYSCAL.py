import ply.lex as lex
from anytree import Node, RenderTree, PreOrderIter
from anytree.exporter import DotExporter
# List of token names.
tokens = (
    'STRING',
    'NUMBER',
    'PLUS',
    'MINUS',
    'TIMES',
    'DIVIDE',
    'LPAREN',
    'RPAREN',
    'LCOLCH',
    'RCOLCH',
    'ID',
    'ATTRIBUTION',
    'DECLARATION',
    'GREATERTHAN',
    'LESSTHAN',
    'EQUALS',
    'DIFFERENT',
    'SEMICOLON',
    'COLON',
    'QUOTES',
    'COMMA',
    'DOT'
)

reserved = {
    'if': 'IF',
    'then': 'THEN',
    'else': 'ELSE',
    'while': 'WHILE',
    'const': 'CONST',
    'var': 'VAR',
    'type': 'TYPE',
    'integer': "INTEGER",
    'real': "REAL",
    'array': "ARRAY",
    'record': "RECORD",
    'of': 'OF',
    'end': 'END',
    'function': "FUNCTION",
    'procedure': "PROCEDURE",
    'begin': "BEGIN",
    'do': "DO",
    'return': "RETURN",
    'write': 'WRITE',
    'read': 'READ'
}

# Regular expression rules for simple tokens
t_STRING = r'\".*\"'
t_PLUS = r'\+'
t_MINUS = r'-'
t_TIMES = r'\*'
t_DIVIDE = r'/'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LCOLCH = r'\['
t_RCOLCH = r'\]'
t_SEMICOLON = r'\;'
t_COLON = r'\:'
t_ATTRIBUTION = r'\:='
t_NUMBER = r'[-]?([0-9]*[.])?[0-9]+'
t_DECLARATION = r'=='
t_GREATERTHAN = r'>'
t_LESSTHAN = r'<'
t_EQUALS = r'='
t_DIFFERENT = r'/!'
t_QUOTES = r'\"'
t_COMMA = r','
t_DOT = r'\.'
t_ignore_COMMENT = r'\#.*'
tokens = list(tokens) + list(reserved.values())


def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value, 'ID')  # Check for reserved words
    return t


# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)


# A string containing ignored characters
t_ignore = ' \t'


# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


# Build the lexer
lexer = lex.lex()

text_file = open("pyscal_code.txt", "r")
data = text_file.read()

# Give the lexer some input
lexer.input(data)

tokens = []
# Tokenize
while True:
    tok = lexer.token()
    if not tok:
        break  # No more input
    tok = [tok.type, tok.value, tok.lineno]
    tokens.append(tok)
print(tokens)
# Analise Sintatica


tokenList = list()
Index = 0
Token = None


def start(list):
    global tokenList, Token
    tokenList = list
    Token = list[0]


def next():
    global tokenList, Token, Index
    tokenAnterior = Token
    tokenList = tokenList[1:]
    if not (confere_tamanho()):
        tokenList = []
        Token = None
        return None

    Token = tokenList[0]
    Index += 1

    return tokenAnterior


def confere_tipo(type):
    global tokenList, Token
    if confere_tamanho() and (Token[0] == type):
        return True
    return False


def confere_tamanho():
    global tokenList
    if (len(tokenList) > 0):
        return True
    return False


def erro(type=None, tokenEsperado=None):
    global Token
    if (type == None) and (tokenEsperado == None):
        print('Erro na linha', {Token[2]})
    elif tokenEsperado == None:
        print(print('Erro', type, 'na linha', {Token[2]}))

    print(f"Erro na regra '{type}', era esperado o token '{tokenEsperado}' na linha {Token[2]}")


def program():
    program_ = Node("PROGRAM")
    declarations(program_)
    bloco(program_)
    return program_


def declarations(parent):
    declarations_ = Node("DECLARATIONS", parent=parent)
    def_const(declarations_)
    def_tipos(declarations_)
    def_var(declarations_)
    def_rot(declarations_)
    return declarations_


def def_const(parent):
    def_const_ = Node("DEF_CONST", parent=parent)
    if confere_tipo('CONST'):
        filho1 = next()
        terminal = Node(filho1[0], parent=def_const_)
        Node(filho1[1], parent=terminal)
        constante(def_const_)
        if confere_tipo('SEMICOLON'):
            filho2 = next()
            terminal = Node(filho2[0], parent=def_const_)
            Node(filho2[1], parent=terminal)
            list_const(def_const_)
            return def_const_
        else:
            erro("DEF_CONST", ";")

    return None


def list_const(parent):
    list_const_ = Node("LIST_CONST", parent=parent)
    filho0 = constante(list_const_)
    if filho0 != None:
        if confere_tipo('SEMICOLON'):
            filho1 = next()
            Node(filho1[0], parent=list_const_)
            list_const(list_const_)
            return list_const_
        else:
            erro("LIST_CONST", ";")

    return None


def constante(parent):
    constante_ = Node("CONSTANTE", parent=parent)
    if confere_tipo('ID'):
        filho0 = next()
        terminal = Node(filho0[0], parent=constante_)
        Node(filho0[1], parent=terminal)
        if confere_tipo('DECLARATION'):
            filho1 = next()
            Node(filho1[0], parent=constante_)
            const_valor(constante_)
            return constante_
        else:
            erro("CONSTANTE", "==")
    return None


def const_valor(parent):
    const_valor_ = Node("CONST_VALOR", parent=parent)
    if confere_tipo('NUMBER') or confere_tipo('ID'):
        exp_mat(const_valor_)
        return parent

    elif confere_tipo('STRING'):
        filho0 = next()
        terminal = Node(filho0[0], parent=const_valor_)
        Node(filho0[1], parent=terminal)
        return const_valor_

    else:
        erro("CONST_VALOR", "STRING | EXP_MAT")

    return None


def def_tipos(parent):
    def_tipos_ = Node("DEF_TIPOS", parent=parent)
    if confere_tipo('TYPE'):
        filho0 = next()
        terminal = Node(filho0[0], parent=def_tipos_)
        Node(filho0[1], parent=terminal)
        tipo(def_tipos_)
        if confere_tipo('SEMICOLON'):
            filho2 = next()
            terminal = Node(filho2[0], parent=def_tipos_)
            Node(filho2[1], parent=terminal)
            list_tipos(def_tipos_)
            return def_tipos_
        else:
            erro("SEMICOLON", ";")

    return None


def list_tipos(parent):
    list_tipos_ = Node("LIST_TIPOS", parent=parent)
    filho0 = tipo(list_tipos_)
    if filho0 != None:
        if confere_tipo('SEMICOLON'):
            filho1 = next()
            terminal = Node(filho1[0], parent=list_tipos_)
            Node(filho1[1], parent=terminal)
            list_tipos(list_tipos_)
            return list_tipos_
        else:
            erro('SEMICOLON', ';')

    return None


def tipo(parent):
    tipo_ = Node("TIPO", parent=parent)
    if confere_tipo('ID'):
        filho0 = next()
        terminal = Node(filho0[0], parent=tipo_)
        Node(filho0[1], parent=terminal)
        if confere_tipo('DECLARATION'):
            filho1 = next()
            terminal = Node(filho1[0], parent=tipo_)
            Node(filho1[1], parent=terminal)
            tipo_dado(tipo_)
            return tipo_
        else:
            erro('DECLARATION', '==')

    return None


def tipo_dado(parent):
    tipo_dado_ = Node("TIPO_DADO", parent=parent)
    if confere_tipo('INTEGER'):
        filho0 = next()
        terminal = Node(filho0[0], parent=tipo_dado_)
        Node(filho0[1], parent=terminal)
        return tipo_dado_

    elif confere_tipo('REAL'):
        filho0 = next()
        terminal = Node(filho0[0], parent=tipo_dado_)
        Node(filho0[1], parent=terminal)
        return tipo_dado_

    elif confere_tipo('ARRAY'):
        array(tipo_dado_)
        return tipo_dado_

    elif confere_tipo('RECORD'):
        filho0 = next()
        terminal = Node(filho0[0], parent=tipo_dado_)
        Node(filho0[1], parent=terminal)
        campos(tipo_dado_)
        if confere_tipo('END'):
            filho2 = next()
            terminal = Node(filho2[0], parent=tipo_dado_)
            Node(filho2[1], parent=terminal)
            return tipo_dado_
        else:
            erro("TIPO_DADO", "end")

    elif confere_tipo('ID'):
        filho0 = next()
        terminal = Node(filho0[0], parent=tipo_dado_)
        Node(filho0[1], parent=terminal)
        return tipo_dado_

    else:
        erro("TIPO_DADO", "integer | real | array | record | ID")

    return None


def array(parent):
    array_ = Node("TIPO_DADO", parent=parent)
    filho0 = next()
    terminal = Node(filho0[0], parent=array_)
    Node(filho0[1], parent=terminal)
    if confere_tipo('LCOLCH'):
        filho1 = next()
        terminal = Node(filho1[0], parent=array_)
        Node(filho1[1], parent=terminal)
        if confere_tipo('NUMBER'):
            filho2 = next()
            terminal = Node(filho2[0], parent=array_)
            Node(filho2[1], parent=terminal)
            if confere_tipo('RCOLCH'):
                filho3 = next()
                terminal = Node(filho3[0], parent=array_)
                Node(filho3[1], parent=terminal)
                if confere_tipo('OF'):
                    filho4 = next()
                    terminal = Node(filho4[0], parent=array_)
                    Node(filho4[1], parent=terminal)
                    tipo_dado(array_)
                    return array_
                else:
                    erro('TIPO_DADO', "of")
            else:
                erro("TIPO_DADO", "]")
        else:
            erro("TIPO_DADO", "numero")
    else:
        erro("TIPO_DADO", "[")

    return None


def campos(parent):
    campos_ = Node("CAMPOS", parent=parent)
    if confere_tipo('ID'):
        filho0 = next()
        terminal = Node(filho0[0], parent=campos_)
        Node(filho0[1], parent=terminal)
        if confere_tipo('COLON'):
            filho1 = next()
            terminal = Node(filho1[0], parent=campos_)
            Node(filho1[1], parent=terminal)
            tipo_dado(campos_)
            lista_campos(campos_)
            return campos_
        else:
            erro("COLON", ":")
    else:
        erro("CAMPOS", "ID")

    return None


def lista_campos(parent):
    lista_campos_ = Node("LISTA_CAMPOS", parent=parent)
    if confere_tipo('SEMICOLON'):
        filho0 = next()
        terminal = Node(filho0[0], parent=lista_campos_)
        Node(filho0[1], parent=terminal)
        campos(lista_campos_)
        lista_campos(lista_campos_)
        return lista_campos_

    return None


def def_var(parent):
    def_var_ = Node("DEF_VAR", parent=parent)
    if confere_tipo('VAR'):
        filho0 = next()
        terminal = Node(filho0[0], parent=def_var_)
        Node(filho0[1], parent=terminal)
        variavel(def_var_)
        if confere_tipo('SEMICOLON'):
            filho2 = next()
            terminal = Node(filho2[0], parent=def_var_)
            Node(filho2[1], parent=terminal)
            list_var(def_var_)
            return def_var_
        else:
            erro("DEF_VAR", ";")

    return None


def list_var(parent):
    list_var_ = Node("LIST_VAR", parent=parent)
    filho0 = variavel(list_var_)

    if filho0 != None:
        if confere_tipo('SEMICOLON'):
            filho1 = next()
            terminal = Node(filho1[0], parent=list_var_)
            Node(filho1[1], parent=terminal)
            list_var(list_var_)
            return list_var_
        else:
            erro("LIST_VAR", ";")
    return None


def variavel(parent):
    variavel_ = Node("VARIAVEL", parent=parent)
    if confere_tipo('ID'):
        filho0 = next()
        terminal = Node(filho0[0], parent=variavel_)
        Node(filho0[1], parent=terminal)
        lista_id(variavel_)
        if confere_tipo('COLON'):
            filho2 = next()
            terminal = Node(filho2[0], parent=variavel_)
            Node(filho2[1], parent=terminal)
            tipo_dado(variavel_)
            return variavel_
        else:
            erro("VARIAVEL", ":")
    return None

def lista_id(parent):
    lista_id_ = Node("PARENT", parent=parent)
    if confere_tipo('COMMA'):
        filho0 = next()
        terminal = Node(filho0[0], parent=lista_id_)
        Node(filho0[1], parent=terminal)
        if confere_tipo('ID'):
            filho1 = next()
            terminal = Node(filho1[0], parent=lista_id_)
            Node(filho1[1], parent=terminal)
            lista_id(lista_id_)
            return lista_id_
        else:
            erro("LISTA_ID", "ID")

    return None


def def_rot(parent):
    def_rot_ = Node("DEF_ROT", parent=parent)
    filho0 = nome_rotina(def_rot_)
    if filho0 != None:
        def_var(def_rot_)
        bloco(def_rot_)
        def_rot(def_rot_)
        return def_rot

    return None


def nome_rotina(parent):
    nome_rotina_ = Node("NOME_ROTINA", parent=parent)
    if confere_tipo('FUNCTION'):
        filho0 = next()
        terminal = Node(filho0[0], parent=nome_rotina_)
        Node(filho0[1], parent=terminal)
        if confere_tipo('ID'):
            filho1 = next()
            terminal = Node(filho1[0], parent=nome_rotina_)
            Node(filho1[1], parent=terminal)
            param_rot(nome_rotina_)
            if confere_tipo('COLON'):
                filho3 = next()
                terminal = Node(filho3[0], parent=nome_rotina_)
                Node(filho3[1], parent=terminal)
                tipo_dado(nome_rotina_)
                return nome_rotina_
            else:
                erro("NOME_ROTINA", ":")
        else:
            erro("NOME_ROTINA", "ID")

    elif confere_tipo('PROCEDURE'):
        filho0 = next()
        terminal = Node(filho0[0], parent=nome_rotina_)
        Node(filho0[1], parent=terminal)
        if confere_tipo('ID'):
            filho1 = next()
            terminal = Node(filho1[0], parent=nome_rotina_)
            Node(filho1[1], parent=terminal)
            param_rot(nome_rotina_)
            return nome_rotina_
        else:
            erro("NOME_ROTINA", "ID")

    return None


def param_rot(parent):
    param_rot_ = Node("PARAM_ROT", parent=parent)
    if confere_tipo('LPAREN'):
        filho0 = next()
        terminal = Node(filho0[0], parent=param_rot_)
        Node(filho0[1], parent=terminal)
        campos(param_rot_)
        if confere_tipo('RPAREN'):
            filho2 = next()
            terminal = Node(filho2[0], parent=param_rot_)
            Node(filho2[1], parent=terminal)
            return param_rot_
        else:
            erro("PARAM_ROT", ")")

    return None


def bloco(parent):
    bloco_ = Node("BLOCO", parent=parent)
    if confere_tipo('BEGIN'):
        filho0 = next()
        terminal = Node(filho0[0], parent=bloco_)
        Node(filho0[1], parent=terminal)
        comando(bloco_)
        if confere_tipo('SEMICOLON'):
            filho2 = next()
            terminal = Node(filho2[0], parent=bloco_)
            Node(filho2[1], parent=terminal)
            lista_com(bloco_)
            if confere_tipo('END'):
                filho4 = next()
                terminal = Node('END', parent=bloco_)
                Node('end', parent=terminal)
                return bloco_
            else:
                erro("BLOCO", "END")
        else:
            erro("BLOCO", ";")

    elif confere_tipo('COLON'):
        filho0 = next()
        terminal = Node(filho0[0], parent=bloco_)
        Node(filho0[1], parent=terminal)
        comando(bloco_)
        return bloco_
    return None


def lista_com(parent):
    lista_com_ = Node("LISTA_COM", parent=parent)
    filho0 = comando(lista_com_)

    if filho0 != None:
        if confere_tipo('SEMICOLON'):
            filho1 = next()
            terminal = Node(filho1[0], parent=lista_com_)
            Node(filho1[1], parent=terminal)
            lista_com(lista_com_)
            return lista_com_
    return None


def comando(parent):
    comando_ = Node("COMANDO", parent=parent)
    if confere_tipo('ID'):
        filho0 = next()
        terminal = Node(filho0[0], parent=comando_)
        Node(filho0[1], parent=terminal)
        nome(comando_)
        atrib(comando_)
        return comando_

    elif confere_tipo('WHILE'):
        filho0 = next()
        terminal = Node(filho0[0], parent=comando_)
        Node(filho0[1], parent=terminal)
        exp_logica(comando_)
        if confere_tipo('DO'):
            filho2 = next()
            terminal = Node(filho2[0], parent=comando_)
            Node(filho2[1], parent=terminal)
            bloco(comando_)
            return comando_
        else:
            erro("COMANDO", "DO")

    elif confere_tipo('IF'):
        filho0 = next()
        terminal = Node(filho0[0], parent=comando_)
        Node(filho0[1], parent=terminal)
        exp_logica(comando_)
        if confere_tipo('THEN'):
            filho2 = next()
            terminal = Node(filho2[0], parent=comando_)
            Node(filho2[1], parent=terminal)
            bloco(comando_)
            else_(comando_)
            return comando_
        else:
            erro("COMANDO", "then")

    elif confere_tipo('RETURN'):
        filho0 = next()
        terminal = Node(filho0[0], parent=comando_)
        Node(filho0[1], parent=terminal)
        exp_logica(comando_)
        return comando_

    elif confere_tipo('WRITE'):
        filho0 = next()
        terminal = Node(filho0[0], parent=comando_)
        Node(filho0[1], parent=terminal)
        exp_mat(comando_)
        return comando_

    elif confere_tipo('READ'):
        filho0 = next()
        terminal = Node(filho0[0], parent=comando_)
        Node(filho0[1], parent=terminal)
        if confere_tipo('ID'):
            filho1 = next()
            terminal = Node(filho1[0], parent=comando_)
            Node(filho1[1], parent=terminal)
            nome(comando_)
            return comando_
        else:
            erro("COMANDO", "ID")

    elif Token == None:
        return None

    return None


def atrib(parent):
    atrib_ = Node("ATRIB", parent=parent)
    if confere_tipo('ATTRIBUTION'):
        filho1 = next()
        terminal = Node(filho1[0], parent=atrib_)
        Node(filho1[1], parent=terminal)
        exp_mat(atrib_)
        return atrib_
    return None


def else_(parent):
    else_ = Node("ELSE", parent=parent)
    if confere_tipo('ELSE'):
        filho0 = next()
        terminal = Node(filho0[0], parent=else_)
        Node(filho0[1], parent=terminal)
        bloco(else_)
        return else_

    return None


def lista_param(parent):
    lista_param_ = Node("LISTA_PARAM", parent=parent)
    if (confere_tipo("RPAREN")):
        return None
    filho0 = parametro(lista_param_)
    if filho0 != None:
        if confere_tipo('COMMA'):
            filho1 = next()
            terminal = Node(filho1[0], parent=lista_param_)
            Node(filho1[1], parent=terminal)
            lista_param(lista_param_)
            return lista_param_

        else:
            return ('LISTA_PARAM', (filho0))
    return None


def op_logico():
    if confere_tipo('LESSTHAN') or confere_tipo('GREATERTHAN') or confere_tipo('EQUALS') or confere_tipo('DIFFERENT'):
        return True


def exp_logica(parent):
    exp_logica_ = Node("EXP_LOGICA", parent=parent)
    exp_mat(exp_logica_)
    if op_logico():
        filho1 = next()
        terminal = Node(filho1[0], parent=exp_logica_)
        Node(filho1[1], parent=terminal)
        exp_logica(exp_logica_)
        return exp_logica_

    else:
        return exp_logica_


def op_mat():
    if confere_tipo('PLUS') or confere_tipo('MINUS') or confere_tipo('TIMES') or confere_tipo('DIVIDE'):
        return True


def exp_mat(parent):
    exp_mat_ = Node("EXP_MAT", parent=parent)
    parametro(exp_mat_)
    if op_mat():
        filho1 = next()
        terminal = Node(filho1[0], parent=exp_mat_)
        Node(filho1[1], parent=terminal)
        exp_mat(exp_mat_)
        return exp_mat_
    else:
        return exp_mat_


def parametro(parent):
    parametro_ = Node("PARAMETRO", parent=parent)
    if confere_tipo('ID'):
        filho0 = next()
        terminal = Node(filho0[0], parent=parametro_)
        Node(filho0[1], parent=terminal)
        nome(parametro_)
        return parametro_

    elif confere_tipo('NUMBER'):
        filho0 = next()
        terminal = Node(filho0[0], parent=parametro_)
        Node(filho0[1], parent=terminal)
        return parametro_

    else:
        erro("PARAMETRO", "ID | NUMERO")

    return None


def nome(parent):
    nome_ = Node("NOME", parent=parent)
    if confere_tipo('DOT'):
        filho0 = next()
        terminal = Node(filho0[0], parent=nome_)
        Node(filho0[1], parent=terminal)
        if confere_tipo("ID"):
            filho1 = next()
            terminal = Node(filho1[0], parent=nome_)
            Node(filho1[1], parent=terminal)
            nome(nome_)
            return nome_
        else:
            erro("NOME", "ID")

    elif confere_tipo('LCOLCH'):
        filho0 = next()
        terminal = Node(filho0[0], parent=nome_)
        Node(filho0[1], parent=terminal)
        parametro(nome_)
        if confere_tipo('RCOLCH'):
            filho2 = next()
            terminal = Node(filho2[0], parent=nome_)
            Node(filho2[1], parent=terminal)
            return nome_
        else:
            erro("NOME", "]")

    elif confere_tipo('LPAREN'):
        filho0 = next()
        terminal = Node(filho0[0], parent=nome_)
        Node(filho0[1], parent=terminal)
        lista_param(nome_)
        if confere_tipo('RPAREN'):
            filho2 = next()
            terminal = Node(filho2[0], parent=nome_)
            Node(filho2[1], parent=terminal)
            return nome_
        else:
            erro("NOME", ")")

    return None


start(tokens)

sintatico = program()

class ItemTabela:

    def __init__(self, nome, classificacao, tipo, escopo, qtd, ordem):
        self.nome = nome
        self.classificacao = classificacao
        self.tipo = tipo
        self.escopo = escopo
        self.qtd = qtd
        self.ordem = ordem

    def __str__(self):
        return f"Nome: {self.nome}, Classificacao: {self.classificacao}, Tipo: {self.tipo}, Escopo: {self.escopo}, Qtd: {self.qtd}, Ordem: {self.ordem}"

tabelaSimbolos = []

escopo = ["global"]
type = ""
classification = ""
isNextID = False
name = ""
lfParameter = False
isNextValue = False
variableValue = ""
mode = "const"
isDeclaring = False
names = []
isSeparated = False
isWaitingForType = False
isNextType = False
waitingForNext = False
isClosingFunction = False
isEndOfFunc = False
isBegOfParamFunc = False
funcName = ""
funcIndex = 0
funcType = ""
isInsideFunction = False
isDeclaringFunctionParam = False
isDeclaringFunctionVariables = False
posAsFuncParam = -1
isFirstBeginInFunctionEscope = True
isInsideProcedure = False
isInMainBlock = False
isWaitingForParameterInExpMat = False
expressionEXPMAT = []
isWaitingForNumber = False
isWaitingForWhatTypeIdIs = False
isWaitingForWhatParameterIs = False
isWatchingForExpMat = False
isAnArray = False
isARecord = False
isType = False
isNextAType = False
isCallingFunction = False
callingParams = []
def isInTable(name, escopoNextParam):
    global tabelaSimbolos
    for x in tabelaSimbolos:
        if(x.nome == name and (x.escopo == escopoNextParam or x.escopo == 'global')):
            return True

def isInGlobalScopeTable(name):
    global tabelaSimbolos
    for x in tabelaSimbolos:
        if (x.nome == name and x.escopo == 'global'):
            return True
    pass

def getTypeID(name, scope):
    global tabelaSimbolos
    for x in tabelaSimbolos:
        if (x.nome == name and (x.escopo == scope or x.escopo == 'global')):
            if (x.tipo != "INTEGER" and x.tipo != "REAL"):
                return getTypeID(x.tipo, scope)
            else:
                return x.tipo

def isItAFunction(name, scope):
    global tabelaSimbolos
    for x in tabelaSimbolos:
        if (x.nome == name and (x.escopo == scope or x.escopo == 'global') and x.classificacao == "funcao"):
            return True


for node in PreOrderIter(sintatico):
    print(node.name)
    print(node)
    if(type == "NUMBER"):
        if ("." in str(name)):
            type = "REAL"
        else:
            type = "INTEGER"
    if (isNextValue):
        isNextValue = False

        if(node.name != "NOME"):
            if(isDeclaring):
                isDeclaring = False
                for Vname in names:
                    if(not isInTable(Vname, escopo[-1])):
                        if (isInsideFunction and (isDeclaringFunctionVariables == False) and (isDeclaringFunctionParam == False)):
                            print(f"A variável '{name}' está sendo utilizada sem a sua declaração!")
                        else:
                            tabelaSimbolos.append(ItemTabela(Vname, classification, type, escopo[-1], None, None))
                    else:
                        print(f"A variável '{name}' ainda não foi declarada!")
                    isSeparated = False
                names = []
            else:
                escopoNextParam = escopo[-1]
                if(isDeclaringFunctionParam and isEndOfFunc):
                    name = funcName
                    classification = "funcao"
                    escopoNextParam = escopo[-2]

                if (not isInTable(name, escopoNextParam)):
                    if(isDeclaringFunctionParam and isEndOfFunc):
                        tabelaSimbolos.append(ItemTabela(name, classification, type, escopoNextParam, posAsFuncParam + 1, None))
                        isEndOfFunc = False
                        isDeclaringFunctionParam = False

                        posAsFuncParam = -1
                    else:
                        if(posAsFuncParam == -1):
                            tabelaSimbolos.append(
                                    ItemTabela(name, classification, type, escopoNextParam, None, None))
                        else:
                            tabelaSimbolos.append(ItemTabela(name, classification, type, escopoNextParam, None, posAsFuncParam))
                    if (classification == "procedure"):
                        escopo.append(name)
                    continue
                else:
                    print("JA ESTA NA TABELA")

    if(node.name == "var" or node.name == "const" or node.name == "type"):
        classification = "variavel"
        continue

    if (isNextID):
        if(node.name == "15"):
            print("inedito")
        if(isDeclaring):
            names.append(node.name)
        else:
            name = node.name
        isNextID = False
        if(classification == "procedure"):
            isNextValue = True
        elif(isDeclaringFunctionParam):
            if(isFuncName):
                isFuncName = False
                funcName = node.name
            else:
                posAsFuncParam += 1
                classification = "parametro"
        elif(not isDeclaringFunctionParam):
            posAsFuncParam = -1
        if (isInsideFunction and (isDeclaringFunctionVariables == False) and (isDeclaringFunctionParam == False)):
            if (not isInTable(name, escopo[-1])):
                print(f"A variável '{node.name}' está sendo utilizada sem a sua declaração!")
        if(isItAFunction(node.name, escopo[-1]) and (not isDeclaringFunctionParam)):
            isCallingFunction = True
            callingParams.append([node.name, escopo[-1], getTypeID(node.name, escopo[-1])])
            continue
        if(isCallingFunction):
            callingParams.append([node.name, escopo[-1], getTypeID(node.name, escopo[-1])])

        continue

    if (isNextType):
        type = node.name
        isNextType = False
        if(type != 'ID'):
            isNextValue = True
        else:
            waitingForNext = True
        isWaitingForType = False
        continue

    if(waitingForNext):
        type = node.name
        isNextValue = True
        waitingForNext = False
        continue

    if(isWaitingForWhatTypeIdIs):
        if(isDeclaring):
            expressionEXPMAT.append([names[-1],getTypeID(names[-1], escopo[-1])])
        else:
            expressionEXPMAT.append([name,getTypeID(name, escopo[-1])])
        isWaitingForWhatTypeIdIs = False
        continue

    if(node.name == 'ID'):
        isNextID = True
        if(isWaitingForWhatParameterIs):
            isWaitingForWhatTypeIdIs = True
        continue

    if (node.name == "procedure"):
        classification = "procedure"
        isInsideProcedure = True
        type = None
        continue

    if (node.name == "ATTRIBUTION"):
        expressionEXPMAT.append([name, getTypeID(name, escopo[-1])])
        isWatchingForExpMat = True
        continue

    if (node.name == "SEMICOLON"):
        if(isWatchingForExpMat):
            isWatchingForExpMat = False
            for x in expressionEXPMAT[1:]:
                if(x[1] != expressionEXPMAT[0][1]):
                    print(f"Erro na declaração: tipos diferentes! Esperado {expressionEXPMAT[0][1]} de {expressionEXPMAT[0][0]}, e recebeu {x[1]} de {x[0]}!")
            print(expressionEXPMAT)
        if(isWaitingForWhatParameterIs):
            isWaitingForWhatParameterIs = False

        expressionEXPMAT = []
        continue

    if(node.name == "LCOLCH"):
        isIndexing = True
        if(isAnArray):
            isDeclaringNumberArray = True

        continue

    if (node.name == "NUMBER" and isWaitingForWhatParameterIs):
        if(isWaitingForWhatParameterIs):
            isWaitingForNumber = True
        continue

    if (isWaitingForNumber):
        isWaitingForNumber = False
        if("." in str(node.name)):
            expressionEXPMAT.append([node.name,'REAL'])
        else:
            expressionEXPMAT.append([node.name,'INTEGER'])
        continue


    if (node.name == "PARAMETRO" and isWatchingForExpMat):
        isWaitingForWhatParameterIs = True
        continue

    if (node.name == "("):
        if(isDeclaringFunctionParam):
            isBegOfParamFunc = True
            escopo.append(funcName)
            funcIndex += 1

        continue

    if (node.name == ")"):
        isEndOfFunc = True
        isDeclaringFunctionVariables = True
        if(isDeclaringFunctionParam):
            isBegOfParamFunc = False
        if(isCallingFunction):
            functionName = callingParams[0][0]
            isCallingFunction = False
            qntdParamFunc = 0
            typesParamFunc = []

            for item in tabelaSimbolos:
                if (item.escopo == functionName and item.classificacao == "parametro"):
                    qntdParamFunc += 1
                    if (item.tipo != 'INTEGER' and item.tipo != 'REAL'):
                        typesParamFunc.append(getTypeID(item.tipo, escopo[-1]))
                    else:
                        typesParamFunc.append(item.tipo)

            a = 0

            if (functionName != ""):
                if (qntdParamFunc > len(callingParams[1:])):
                    print(f"Erro. Numero de parametros menor que o esperado na funcao {functionName}. Era esperado {qntdParamFunc} parâmetros e foi recebido {len(callingParams[1:])}")
                elif (qntdParamFunc < len(callingParams[1:])):
                    print(f"Erro. Numero de parametros maior que o esperado na funcao {functionName}. Era esperado {qntdParamFunc} parâmetros e foi recebido {len(callingParams[1:])}")
                else:
                    for item in callingParams[1:]:
                        if (typesParamFunc[a] == item[2]):
                            a += 1
                        else:
                            print(f"Erro no tipo de parametro passado para a funcao {functionName}")
                            break

            callingParams = []

        continue

    if(node.name == "COMMA" and (isSeparated == False)):
        isDeclaring = True
        names.append(name)
        isSeparated = True
        continue

    if(node.name == "array"):
        classification = "ARRAY"
        isAnArray = True
        continue

    if(node.name == "COLON"):
        isWaitingForType = True
        continue

    if(node.name == "TIPO_DADO"):
        if(isNextAType):
            isNextType = True
            isNextAType = False
            continue
        if(isAnArray):
            isNextType = True
            isAnArray = False
            continue
        if(isWaitingForType or (isDeclaringFunctionParam and isEndOfFunc)):
            isNextType = True
            continue
        classification = "variavel"
        continue

    if(node.name == "function"):
        isFuncName = True
        isDeclaringFunctionParam = True
        isFirstBeginInFunctionEscope = True
        classification = "function"
        isInsideFunction = True
        continue

    if (node.name == "begin"):
        if(isFirstBeginInFunctionEscope):
            isFirstBeginInFunctionEscope = False
            isDeclaringFunctionVariables = False
            continue
        else:
            if(not(isInsideFunction or isInsideProcedure)):
                isInMainBlock = True
            escopo.append(funcName)
            funcIndex += 1
            continue


    if (node.name == "end"):
        escopo.pop()
        if(isInsideFunction and escopo[-1] == "global"):
            isInsideFunction = False
        funcIndex -= 1

        if(isInsideProcedure and escopo[-1] == "global"):
            isInsideProcedure = False

        if(isInMainBlock and escopo[-1] == "global"):
            isInMainBlock = False
        continue

    if(node.name == "record"):
        escopo.append(name)
        continue

    if (node.name == 'PARAMETRO'):
        lfParameter = True
        continue

    if(node.name == "STRING"):
        isNextValue = True
        type = "STRING"
        continue

    if (lfParameter):
        lfParameter = False
        if(node.name == "ID"):
            isNextID = True
        if (node.name == "NUMBER"):
            isNextValue = True
            type = "NUMBER"
            continue
        continue




print("differences")

for x in tabelaSimbolos:
    print(x)