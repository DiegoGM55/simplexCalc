// *** ERROR HANDLING
window.onerror = myErrorTrap;

let epsilon = 0.00000000000001; // 10^-14
let maxSigDig = 13; // número máximo de dígitos significativos

let okToRoll = true; // resultados preliminares dos testes
let stepName = ""; // para capturar erros

// Símbolos especiais
const tab = '\t';
const cr = '\r';
const lf = '\n';
const symb = 'Å';
const backSlash = '\\';
const gteSymbol = '³'; // Símbolos em navegadores antigos
const lteSymbol = '²';
const lte = '\u2264'; // Símbolo real no IE
const gte = '\u2265';
const comma = ',';

let singular = false;
let msFormat = false;
let maxRows = 15;
let maxCols = 30;
let numRows = 0;
let numCols = 0;
let numConstraints = 0;
let maximization = true; // este é um problema de maximização
let phase1 = false; // estamos na fase 1?
let objectiveName = "p";
let numVariables = 1;
let variables = [];
let theTableau = new makeArray2(1, 1);
let theStringTableau = new makeArray2(1, 1); // para exibir as etapas do cálculo
let starred = new makeArray(1); // linhas marcadas
let TableauNumber = 1; // o número de tabelas
let maxSteps = 50; // número máximo de tabelas
let numSigDigs = 6; // precisão padrão
let activeVars = new Array(); // variáveis ativas

// Antigas variáveis globais
let maxDenom = 1000;
let tol = 0.000000001;
let tooBigString = "Muitas matrizes em sua expressão," +
	cr +
	"ou sua expressão está muito complicada." +
	cr +
	"Por favor, mantenha-a simples!";

// Strings de exemplo e instruções
let theSampleLPString =
	"Maximizar p = (1/2)x + 3y + z + 4w sujeito a:" +
	cr +
	"x + y + z + w <= 40" +
	cr +
	"2x + y - z - w >= 10" +
	cr +
	"w - y >= 10";

let theInstructionString =
	"Notas sobre formatação: " +
	cr +
	" (1) Nomes de variáveis devem começar com letras." +
	cr +
	tab +
	tab +
	"    (ex. p, x1, loss, z, s, t, u...) " +
	cr +
	" (2) Para entradas fracionárias, mantenha a variável à direita." +
	cr +
	tab +
	tab +
	"    (ex. (1/3)x e não x/3) " +
	cr +
	" (3) Cada variável que você usar deve aparecer na função objetiva, (mas não" +
	cr +
	"     necessariamente nas restrições). " +
	cr +
	tab +
	tab +
	"    (ex. p = 0x + 2y + 0z ) " +
	cr +
	" (4) As palavras 'Maximizar' (ou 'minimizar') e 'sujeito a:' devem aparecer. " +
	cr +
	" (5) Cada desigualdade deve estar em sua própria linha, como mostrado. " +
	cr +
	" (6) Não é necessário inserir as restrições padrão: x >= 0, y >= 0, z >= 0 etc.";


let fractionMode = false;
let integerMode = false;


// ****************** ERRO *************

function myErrorTrap() {
	alert(
		"Ocorreu um erro." +
			cr +
			" Clique em 'Exemplo' para ver como inserir um problema." 
	);

	return true;
} 

// ******************* UTILITÁRIOS MATEMÁTICOS *******************

function hcf(a, b) {
	let bigger = Math.abs(a);
	let smaller = Math.abs(b);
	let x = 0;
	let theResult = 1;
  
	if (a == 0 || b == 0) return 1;
  
	if (smaller > bigger) {
	  [bigger, smaller] = [smaller, bigger];
	}
  
	let testRatio = roundSigDig(bigger / smaller, 11);
	let testRatio2 = 0;
  
	if (testRatio == Math.floor(testRatio)) return smaller;
	else {
	  let found = false;
	  let upperlimit = smaller;
  
	  for (let i = upperlimit; i >= 2; i--) {
		testRatio = roundSigDig(smaller / i, 10);
		testRatio2 = roundSigDig(bigger / i, 10);
  
		if (testRatio == Math.floor(testRatio) && testRatio2 == Math.floor(testRatio2)) {
		  smaller = Math.round(smaller / i);
		  bigger = Math.round(bigger / i);
		  return theResult * hcf(bigger, smaller);
		}
	  }
  
	  return theResult;
	}
  }
  
  function lcm(a, b) {
	let bigger = Math.abs(a);
	let smaller = Math.abs(b);
	let x = 0;
  
	if (a == 0 || b == 0) return 1;
  
	if (smaller > bigger) {
	  [bigger, smaller] = [smaller, bigger];
	}
  
	let testRatio = roundSigDig(bigger / smaller, 11);
  
	if (testRatio == Math.floor(testRatio)) return bigger;
	else {
	  for (let i = 2; i <= smaller; i++) {
		if (i * i >= smaller) break;
  
		testRatio = roundSigDig(smaller / i, 11);
  
		if (testRatio == Math.floor(testRatio)) {
		  smaller = testRatio;
		  bigger = bigger * i;
		  return lcm(bigger, smaller);
		}
	  }
  
	  return bigger * smaller;
	}
  }
  
  function reduce(fraction) {
	const HCF = hcf(fraction[1], fraction[2]);
	fraction[1] = Math.round(fraction[1] / HCF);
	fraction[2] = Math.round(fraction[2] / HCF);
	return fraction;
  }
  
  function toFracArr(x, maxDenom, tol) {
	let theFrac = [0, 0];
	let p1 = 1,
	  p2 = 0,
	  q1 = 0,
	  q2 = 1,
	  u = 0,
	  t = 0,
	  flag = true,
	  negflag = false,
	  a = 0,
	  xIn = x;
  
	if (x > 10000000000) return theFrac;
  
	while (flag) {
	  if (x < 0) {
		x = -x;
		negflag = true;
		p1 = -p1;
	  }
  
	  let intPart = Math.floor(x);
	  let decimalPart = roundSigDig(x - intPart, 15);
  
	  x = decimalPart;
	  a = intPart;
	  t = a * p1 + p2;
	  u = a * q1 + q2;
  
	  if (Math.abs(t) > 10000000000 || u > maxDenom) {
		theFrac[1] = p1;
		theFrac[2] = q1;
		break;
	  }
  
	  let p = t;
	  let q = u;
  
	  if (x == 0) {
		theFrac[1] = p;
		theFrac[2] = q;
		break;
	  }
  
	  [p2, p1, q2, q1] = [p1, p, q1, q];
	  x = 1 / x;
	}
  
	return theFrac;
  }
  
  function toFrac(x, maxDenom, tol) {
	let theFrac = [0, 0];
	let p1 = 1,
	  p2 = 0,
	  q1 = 0,
	  q2 = 1,
	  u = 0,
	  t = 0,
	  flag = true,
	  negflag = false,
	  a = 0,
	  xIn = x;
  
	if (x > 10000000000) return theFrac;
  
	while (flag) {
	  if (x < 0) {
		x = -x;
		negflag = true;
		p1 = -p1;
	  }
  
	  let intPart = Math.floor(x);
	  let decimalPart = roundSigDig(x - intPart, 15);
  
	  x = decimalPart;
	  a = intPart;
	  t = a * p1 + p2;
	  u = a * q1 + q2;
  
	  if (Math.abs(t) > 10000000000 || u > maxDenom) {
		theFrac[1] = p1;
		theFrac[2] = q1;
		break;
	  }
  
	  let p = t;
	  let q = u;
  
	  if (x == 0) {
		theFrac[1] = p;
		theFrac[2] = q;
		break;
	  }
  
	  [p2, p1, q2, q1] = [p1, p, q1, q];
	  x = 1 / x;
	}
  
	if (theFrac[2] == 1) return theFrac[1].toString();
	else return theFrac[1] + "/" + theFrac[2];
  }
  
  function lastChar(theString) {
	if (theString == "") return theString;
	return theString.charAt(theString.length - 1);
  }
  
  function isCharHere(InString, RefString) {
	if (InString.length != 1) return false;
	return RefString.indexOf(InString, 0) !== -1;
  }
  
  function looksLikeANumber(theString) {
	const length = theString.length;
	if (length === 0) return false;
  
	const validChars = "1234567890-+*. /";
	for (let i = 0; i < length; i++) {
	  if (validChars.indexOf(theString.charAt(i)) === -1) {
		return false;
	  }
	}
	return true;
  }
  
  function roundSix(theNumber) {
	return Math.round(1000000 * theNumber) / 1000000;
  }
  
  function shiftRight(theNumber, k) {
	if (k === 0) return theNumber;
  
	let k2 = 1;
	let num = Math.abs(k);
  
	for (let i = 1; i <= num; i++) {
	  k2 = k2 * 10;
	}
  
	return k > 0 ? k2 * theNumber : theNumber / k2;
  }
  
  function roundSigDig(theNumber, numDigits) {
	numDigits = numDigits - 1;
  
	if (theNumber === 0 || Math.abs(theNumber) < 0.000000000001) return 0;
  
	let k = Math.floor(Math.log(Math.abs(theNumber)) / Math.log(10)) - numDigits;
	let k2 = shiftRight(Math.round(shiftRight(Math.abs(theNumber), -k)), k);
  
	return theNumber > 0 ? k2 : -k2;
  }
  
// *******************PIVO **********************

function pivot(InMatrix, rows, cols, theRow, theCol) {
	// O elemento pivô é o valor na posição (theRow, theCol)
	var thePivot = InMatrix[theRow][theCol];
  
	// Atualiza a variável ativa para a coluna do pivô
	activeVars[theRow] = theCol;
  
	// Remove a estrela da linha pivô
	starred[theRow] = 0;
  
	// Normaliza a linha pivô dividindo todos os elementos pelo pivô
	for (var i = 1; i <= cols; i++) {
	  InMatrix[theRow][i] = InMatrix[theRow][i] / thePivot;
	}
  
	// Realiza o pivoteamento nas outras linhas
	for (var i = 1; i <= rows; i++) {
	  // Ignora a linha pivô e as linhas com valor zero na coluna do pivô
	  if (i != theRow && InMatrix[i][theCol] != 0) {
		var factr = InMatrix[i][theCol];
  
		// Atualiza os elementos da linha usando o pivoteamento
		for (var j = 1; j <= cols; j++) {
		  InMatrix[i][j] =
			roundSigDig(InMatrix[i][j], maxSigDig + 2) -
			roundSigDig(factr * InMatrix[theRow][j], maxSigDig + 2);
		}
	  }
	}
  
	// Retorna a matriz resultante após o pivoteamento
	return InMatrix;
  }

// ***************** Fim Pivo *********************

// ****************SIMPLEX ****************

function simplexMethod(InMatrix, rows, cols) {
	var negIndicator = false; // Indica se há algum número negativo na última linha do tableau.
	var testRatio = new Array(); // Array para armazenar razões a serem consideradas durante o pivoteamento.
	var theRow = 0; // Índice da linha escolhida para o pivoteamento.
	singular = false; // Indica se o problema é singular.
	
	document.theSpreadsheet.expr.value = "trabalhando...";
	
	// Fase I
	while (phase1 && TableauNumber <= maxSteps) {
	  // Código removido para economizar espaço
	  
	  // Primeiro, remova a estrela de todas as linhas com zeros no lado direito,
	  // invertendo as desigualdades.
	  var checkingForZeros = true;
	  var foundAZero = false;
	  
	  while (checkingForZeros) {
		checkingForZeros = false;
		
		for (var i = 1; i <= numRows - 1; i++) {
		  if (starred[i] == 1) break;
		}
		theRowx = i;
		
		// Verifica se o primeiro elemento da linha é zero no lado direito
		if (roundSigDig(InMatrix[theRowx][cols], maxSigDig) == 0)
		  InMatrix[theRowx][cols] = 0;
  
		if (InMatrix[theRowx][cols] == 0 && starred[theRowx] == 1) {
		  checkingForZeros = true;
		  foundAZero = true;
		  
		  // Inverte os sinais dos elementos da linha
		  for (var j = 1; j <= cols - 1; j++) {
			InMatrix[theRowx][j] *= -1;
		  }
		  
		  starred[theRowx] = 0;
		  TableauNumber += 1;
		  document.theSpreadsheet.expr.value += "..";
		  displayMatrix(1);
		}
	  }
	  
	  // Verifica se há linhas marcadas com estrela
	  phase1 = false;
	  for (var i = 1; i <= numConstraints; i++) {
		if (starred[i] == 1) {
		  phase1 = true;
		  break;
		}
	  }
  
	  if (phase1) {
		if (!foundAZero) {
		  var rowmax = 0;
		  
		  for (i = 1; i <= numRows - 1; i++) {
			if (starred[i] == 1) break;
		  }
		  theRowx = i;
  
		  // Encontra o maior valor positivo na primeira linha marcada com estrela
		  for (var j = 1; j <= numCols - 2; j++) {
			numx = roundSigDig(InMatrix[i][j], 10);
			
			if (numx > rowmax) {
			  rowmax = numx;
			  theColx = j;
			}
		  }
  
		  if (rowmax == 0) {
			singular = true;
			displayFinalStatus();
			return InMatrix;
		  } else {
			// Calcula a razão mais baixa e faz o pivoteamento na linha theRowx, coluna theColx
			for (var i = 1; i <= rows - 1; i++) {
			  testRatio[i] = -1;
			  
			  if (roundSigDig(InMatrix[i][theColx], maxSigDig) > 0) {
				if (Math.abs(InMatrix[i][cols]) < epsilon) InMatrix[i][cols] = 0;
				testRatio[i] = InMatrix[i][cols] / InMatrix[i][theColx];
			  }
			}
			
			var minRatio = 10000000000000;
			theRow = 0;
			
			for (var i = 1; i <= rows - 1; i++) {
			  if (testRatio[i] >= 0 && testRatio[i] < minRatio) {
				minRatio = testRatio[i];
				theRow = i;
			  } else if (testRatio[i] >= 0 && testRatio[i] == minRatio) {
				if (starred[i] == 1) theRow = i;
				else if (Math.random() > 0.5) theRow = i;
			  }
			}
  
			// Tratamento de escape
			if (theRow == 0) {
			  singular = true;
			  displayFinalStatus();
			  return InMatrix;
			}
  
			InMatrix = pivot(InMatrix, rows, cols, theRow, theColx);
			TableauNumber += 1;
			document.theSpreadsheet.expr.value += "..";
			displayMatrix(1);
		  }
		}
	  }
	}
  
	// Fim da Fase I
  
	// Fase II
	var testnum = 0;
  
	for (var i = 1; i <= cols - 1; i++) {
	  testnum = roundSigDig(InMatrix[rows][i], 10);
  
	  if (testnum < 0) {
		negIndicator = true;
	  }
	}
  
	var theCol = 0;
  
	if (negIndicator) {
	  var minval = 0;
  
	  for (i = 1; i <= cols - 1; i++) {
		testnum = roundSigDig(InMatrix[rows][i], 10);
  
		if (testnum < minval) {
		  minval = testnum;
		  theCol = i;
		}
	  }
	}
  
	while (negIndicator && TableauNumber <= maxSteps) {
	  for (var i = 1; i <= rows - 1; i++) {
		testRatio[i] = -1;
		
		if (roundSigDig(InMatrix[i][theCol], maxSigDig) > 0) {
		  if (Math.abs(InMatrix[i][cols]) < epsilon) InMatrix[i][cols] = 0;
		  testRatio[i] = InMatrix[i][cols] / InMatrix[i][theCol];
		}
	  }
  
	  var minRatio = 10000000000000;
	  theRow = 0;
  
	  for (var i = 1; i <= rows - 1; i++) {
		if (testRatio[i] >= 0 && testRatio[i] < minRatio) {
		  minRatio = testRatio[i];
		  theRow = i;
		} else if (testRatio[i] >= 0 && testRatio[i] == minRatio) {
		  if (Math.random() > 0.5) theRow = i;
		}
	  }
  
	  if (theRow == 0) {
		singular = true;
		displayFinalStatus();
		return InMatrix;
	  }
  
	  InMatrix = pivot(InMatrix, rows, cols, theRow, theCol);
	  TableauNumber += 1;
	  document.theSpreadsheet.expr.value += "..";
	  displayMatrix(1);
	  
	  negIndicator = false;
  
	  for (var i = 1; i <= cols - 1; i++) {
		if (roundSigDig(InMatrix[rows][i], 10) < 0) {
		  negIndicator = true;
		}
	  }
  
	  if (negIndicator) {
		var minval = 0;
  
		for (i = 1; i <= cols - 1; i++) {
		  testnum = roundSigDig(InMatrix[rows][i], 10);
  
		  if (testnum < minval) {
			minval = testnum;
			theCol = i;
		  }
		}
	  }
	}
  
	displayFinalStatus();
	return InMatrix;
  }

// ********************** FIM SIMPLEX **********************

function checkString(InString, subString, backtrack) {
	// check for subString

	// if backtrack = false, returns -1 if not found, and left-most location in string if found

	// if backtrack = true, returns -1 if not found, and right-most location in string if found

	// note that location is to the left of the substring in both cases

	var found = -1;

	var theString = InString;

	var Length = theString.length;

	var symbLength = subString.length;

	for (var i = Length - symbLength; i > -1; i--) {
		TempChar = theString.substring(i, i + symbLength);

		if (TempChar == subString) {
			found = i;

			if (backtrack) i = -1;
		}
	} // i

	return found;
} // check

function parser(InString, Sep) {
	// ************************

	// returns an array 0th entry = number n of blocks (-1) if the character Sep does not occur

	// subsequent n entries are the blocks themselves

	// Here are the blocks

	// ***block 1 *** SEP *** block 2 *** SEP *** block 3 ***

	// (one more block than number of occurrences of SEP)

	// ************************

	var NumSeps = 0;
	var Count = 0;

	var location = new Array();

	location[0] = -1;

	var len = InString.length;

	for (Count = 0; Count < len; Count++) {
		if (InString.charAt(Count) == Sep) {
			NumSeps++;

			location[NumSeps] = Count;
		}
	}

	var parse = new makeArray(NumSeps + 2);

	if (NumSeps == 0) {
		parse[0] = 1;
		parse[1] = InString;
		return parse;
	}

	parse[0] = NumSeps + 1;

	for (var i = 1; i <= NumSeps; i++) {
		parse[i] = InString.substring(location[i - 1] + 1, location[i]);

		// alert("i = " + i + "  "  + parse[i]);
	}

	parse[NumSeps + 1] = InString.substring(location[NumSeps] + 1, len);

	// alert("i = " + i + "  "  + parse[i]);

	return parse;
}

function parseLinearExpr(InString) {
	// **********

	// Returns an array: with 0th entry = an array of variable names

	// (eg. ["x", "x'", "y", "z"])

	// and subsequent entries the coefficients.

	// to get the number of coefficients, just take the length of the array in position 0.

	// first remove a leading cr if there

	InString = stripChar(InString, "("); // get rid of parens (not needed once x is gone...

	InString = stripChar(InString, ")");

	var stringlen = InString.length;

	// alert(escape(InString.charAt(0)));

	// if (InString.charAt(0) == unescape( "%0A" )) InString = InString.substring(1, stringlen);

	// THE ABOVE LINE REMOVES A STRANGE BUG IN NETSCAPE, WHICH SEEMS

	// TO INSERT A SPURIOUS LINE BREAK  (0A) THERE RATHER THAN A CR (0D)

	// first insert a leading 1

	// ***HERE THE FOLLOWING LINE WAS ADDED AS A FIX FOR WINTEL

	if (!looksLikeANumber(InString.charAt(0))) InString = "1" + InString;

	// first insert a leading + if necessary

	if (InString.charAt(0) != "-") InString = "+" + InString;

	// alert(InString);

	var variableList = "";

	InString = replaceSubstring(InString, "+", "_+");

	InString = replaceSubstring(InString, "-", "_-");

	var ch = "_";

	var Ar = parser(InString, ch);

	var parsd = new makeArray(Ar[0] + 1, "");

	// alert(Ar[0] + "***" + Ar[1] + "***" + Ar[2] + "***" + Ar[3] + "***" + Ar[4] );

	for (var i = 1; i < Ar[0]; i++) {
		parsd[i] = stripChar(Ar[i + 1], "_");

		// parser gives 1st entry as what is before first sign -- ignore it
	}

	// now for the variable names

	var vars = [];

	for (var i = 1; i < Ar[0]; i++) {
		vars[i - 1] = /([a-zA-Z].*)/.exec(parsd[i])[1];

		parsd[i] = parsd[i].replace(/[a-zA-Z].*/, "");

		if (parsd[i] == "+") parsd[i] = "1"; // fix up the coefficients
		else if (parsd[i] == "-") parsd[i] = "-1";

		parsd[i] = stripChar(parsd[i], "+");
	}

	parsd[0] = vars;

	// alert(parsd[0] + "," + parsd[1] + "," + parsd[2] + "," + parsd[3])

	return parsd;
} // parser

function rightString(InString, num) {
	OutString = InString.substring(InString.length - num, InString.length);

	return OutString;
}

function rightTrim(InString) {
	var length = InString.length;

	OutString = InString.substring(0, length - 1);

	return OutString;
}

function replaceChar(InString, oldSymbol, newSymbol) {
	var OutString = "";

	var TempChar = "";

	for (Count = 0; Count < InString.length; Count++) {
		TempChar = InString.substring(Count, Count + 1);

		if (TempChar != oldSymbol) OutString = OutString + TempChar;
		else OutString = OutString + newSymbol;
	}

	return OutString;
}

function replaceSubstring(InString, oldSubstring, newSubstring) {
	OutString = "";

	var sublength = oldSubstring.length;

	for (Count = 0; Count < InString.length; Count++) {
		TempStr = InString.substring(Count, Count + sublength);

		TempChar = InString.substring(Count, Count + 1);

		if (TempStr != oldSubstring) OutString = OutString + TempChar;
		else {
			OutString = OutString + newSubstring;

			Count += sublength - 1;
		}
	}

	return OutString;
}

// ******************** FORM UTILITIES ******************

function sesame(url, hsize, vsize) {
	// Default size is 550 x 400

	var tb = "toolbar=0,directories=0,status=0,menubar=0";

	tb += ",scrollbars=1,resizable=1,";

	var tbend = "width=" + hsize + ",height=" + vsize;

	if (tbend.indexOf("<undefined>") != -1) {
		tbend = "width=550,height=400";
	}

	tb += tbend;

	Win_1 = window.open("", "win1", tb);

	Win_1 = window.open(url, "win1", tb);
}

// ******************* LP PARSER FOLLOWS  **************************

function SetupTableau() {
	// reads problem and sets up the first tableau

	// get out of here if not ok

	if (!okToRoll) return 666;

	// first, adjust some globals...

	maximization = true;

	singular = false; // start with a clean slate

	var theString = document.theSpreadsheet.input.value;

	theString += cr; // want an extra cr at the end

	theString = stripSpaces(theString);

	theString = stripChar(theString, tab); // get rid of tabs

	theString = stripChar(theString, ":"); // get rid of colons

	theString = replaceSubstring(theString, lf, cr); // replace line feeds by carriage returns

	// some browsers add these to cr

	// convert everything to lower case

	theString = theString.toLowerCase();

	// now parse commas into line breaks and introduce a line break after "sujeito a"

	theString = replaceSubstring(theString, "a:", "a:" + cr);

	theString = replaceSubstring(theString, ",", cr);

	theString = replaceSubstring(theString, cr + "sujeito", "sujeito"); // in case they have introduced a line break or comma before 'sujeito a'

	console.log(theString);

	// now get rid of double carriage returns

	var doublecr = true;

	while (doublecr) {
		if (checkString(theString, cr + cr, false) == -1) doublecr = false;
		else theString = replaceSubstring(theString, cr + cr, cr);
	}

	console.log(checkString(theString, cr + cr, false));

	// get rid of terminating cr

	if (lastChar(theString) == cr) theString = rightTrim(theString, 1);

	// else alert("*"+lastChar(theString)+"*");

	theString = replaceSubstring(theString, "<=", lteSymbol);

	theString = replaceSubstring(theString, ">=", gteSymbol);

	theString = replaceSubstring(theString, lte, lteSymbol);

	theString = replaceSubstring(theString, gte, gteSymbol);

	// look for "maximize" and chop the string there

	var check = checkString(theString, "maxi", false);



	if (check == -1) {
		check = checkString(theString, "mini", false);
		maximization = false;
		phase1 = true;
	}

	if (check == -1) {
		document.theSpreadsheet.expr.value = "Huh?";
		document.theSpreadsheet.output.value =
			"Isso não parece um problema de programação linear!" +
			cr +
			cr +
			"Clique em exemplo para ver como entrar com o problema.";
		okToRoll = false;
		return 666;
	}

	len = theString.length;

	theString = theString.substring(check, len);

	// now the string starts with "max or "min"

	// now extract the objective and constraints

	var tempAr = parser(theString, cr);

	var numConstTemp = tempAr[0] - 1;
	//alert(numConstTemp);
	for (var i = 2; i <= numConstTemp + 1; i++) {
		if (tempAr[i] && tempAr[i].match(/=/)) {
			tempAr[i] = tempAr[i].replace(/=/, lteSymbol);

			tempAr[numConstTemp + 2] = tempAr[i].replace(lteSymbol, gteSymbol);
			numConstTemp += 1;
			tempAr[0] += 1;
		}
	}

	// alert("HERElines of the problem are: "+tempAr[0] + " blocks " + tempAr[1] + " \n" + tempAr[2] + "\n" + tempAr[3] + "\n" +  tempAr[4] + " \n " +  tempAr[5] + "***")

	// the first line should contain the objective

	var line1 = tempAr[1];

	// get rid of "sujeito a, if there"

	console.log(line1);

	check = checkString(line1, "sujeito", true);

	if (check > 0) line1 = line1.substring(0, check);

	// now look for objective

	check = checkString(line1, "=", false);

	if (check <= 0) return 666;

	objectiveName = line1.charAt(check - 1);

	len = line1.length;

	var expression = line1.substring(check + 1, len);

	// alert(expression);

	var OBJ = parseLinearExpr(expression);

	variables = OBJ[0];

	// alert (variables);

	numConstraints = tempAr[0] - 1;

	// alert(numConstraints+1);

	// make the tableau .. note that all the variables are assumed to appear in the objective!!!

	numVariables = variables.length;

	// alert("number of variables =" +  numVariables)

	numRows = numConstraints + 1;

	numCols = numRows + numVariables + 1;

	// create the tableau

	theTableau = new makeArray2(numRows, numCols);

	theStringTableau = new makeArray2(numRows, numCols); // for display purposes

	if (phase1) starred = new makeArray(numRows); // for starred rows

	// do the last row

	for (var j = 1; j <= numCols; j++) theTableau[numRows][j] = 0; // init

	for (var i = 1; i <= numVariables; i++) {
		if (maximization) theTableau[numRows][i] = -eval(OBJ[i]);
		else theTableau[numRows][i] = eval(OBJ[i]);
	}

	theTableau[numRows][numCols - 1] = 1;

	theTableau[numRows][numCols] = 0;

	// now extract the constraints

	// first remove the "sujeito a..."

	theString = tempAr[2];

	var x = checkString(theString, "a:", false);

	len = theString.length;

	if (x != -1) theString = theString.substring(x + 2, len);

	// alert(theString);

	tempAr[2] = theString;

	var GTE = false; // greater-than-eq flag

	// alert("num constraints is " + numConstraints )

	for (var i = 1; i <= numConstraints; i++) {
		activeVars[i] = i + numVariables;
		starred[i] = 0;

		GTE = false; // clean slate
		// alert(tempAr[1+i]);
		// first get the inequalities out of the way
		twoPart = parser(tempAr[1 + i], lteSymbol);

		if (twoPart[0] < 2) {
			// alert(tempAr[1+i]);
			twoPart = parser(tempAr[1 + i], gteSymbol);
			phase1 = true;
			GTE = true;
		}

		if (twoPart[0] < 2) {
			// alert(tempAr[1+i]);
			i += 1;

			okToRoll = false;

			document.theSpreadsheet.expr.value =
				"Huh? The expression in line " +
				i +
				" does not look like an inequality to me!";

			// alert("left-side of inequality = " + twoPart[1]);

			return 666;
		}

		// alert("left-side of ineuqulaity = " + twoPart[1]);

		// alert(twoPart[2]);

		var leftHandSide = parseLinearExpr(twoPart[1]);

		for (var j = 1; j <= numCols; j++) theTableau[i][j] = 0; // init

		theTableau[i][numCols] = eval(twoPart[2]); // the right-hand side

		if (GTE) {
			theTableau[i][numVariables + i] = -1;
			starred[i] = 1;
			phase1 = true;
		} else theTableau[i][numVariables + i] = 1;

		var theIndex = 0;

		for (var j = 1; j <= numVariables; j++) {
			theVar = variables[j - 1];

			theIndex = -1;

			for (var k = 0; k < leftHandSide[0].length; k++) {
				if (leftHandSide[0][k] == theVar) {
					theIndex = k;

					break;
				}
			}

			// if (i == 3) alert(theIndex);

			if (theIndex == -1) theTableau[i][j] = 0;
			else theTableau[i][j] = eval(leftHandSide[theIndex + 1]);

			// alert("HERE");
		}
	} // enf of the loop i

	// alert("HERE")

	// *** testing starts *******HERE

	// var display = "\r";

	// for (var i = 1; i <= numRows; i++)

	//	{

	//	for (j = 1; j <= numCols; j++)

	//		{

	//		display += theTableau[i][j]  + tab;

	//		} // j

	//	display += cr;

	//	} // i

	// document.theSpreadsheet.output.value += display;

	// alert("Pausing");

	// *** testing *******

	displayMatrix(1);

	// *** testing *******

	// document.theSpreadsheet.output.value = "objective name = " + objectiveName + cr +  "the expression = " + expression;

	// alert ("pausing");

	// *** testing *******

	return 1;
} // SetupTableau

function displayFinalStatus() {
	// gives the solution or error messages

	if (TableauNumber > maxSteps)
		document.theSpreadsheet.expr.value =
			"Nenhuma solução encontrada em " + maxSteps + " passos.";
	else if (singular)
		document.theSpreadsheet.expr.value =
			"Não existe solução ótima. O problema é ilimitado.";
	else {
		document.theSpreadsheet.expr.value =
			"Solução ótima: " + objectiveName + " = ";

		var numx = 0;
		var theRowx = 0;
		var theColx = 0;
		var count = 0;
		var theChar = "";

		var theStr = "";

		var objectiveVal = theTableau[numRows][numCols];

		if (!maximization) objectiveVal = -objectiveVal;

		if (fractionMode || integerMode)
			document.theSpreadsheet.expr.value +=
				toFrac(roundSigDig(objectiveVal, 15), maxDenom, tol) + "; ";
		else
			document.theSpreadsheet.expr.value +=
				roundSigDig(objectiveVal, numSigDigs).toString() + "; ";

		var thePivotPosn = new Array();
		var useThis = true;
		for (var j = 1; j <= numVariables; j++) {
			useThis = true;
			count = 0;

			theRowx = 0;

			theChar = variables[j - 1]; // name of this variable
			thePivotPosn[j] = 0;
			useThis = true;
			document.theSpreadsheet.expr.value += theChar + " = ";
			//alert([numRows,numVariables])
			for (var i = 1; i <= numRows; i++) {
				numx = roundSigDig(theTableau[i][j], 10);
				if (numx != 0) {
					count++; // counting number of bnonzero entries in the column
					if (numx != 0) theRowx = i;
				}
			} // i
			//alert(theRowx)
			if (count == 1 && roundSigDig(theTableau[theRowx][j], 10) > 0) {
				// correction May 20 2010 he second condition above did not check that the pivot was positive!!!
				thePivotPosn[j] = theRowx; // row of that pivot
				// check if we have not already used a pivot in that row
				// in the case of more than one pivot per row
				if (theRowx == numRows) useThis = false; // Fix 02 added this line. Reason: (positive) pivot in the bottom row indicates that that variable is zero
				for (var u = 1; u <= j - 1; u++)
					if (thePivotPosn[j] == thePivotPosn[u]) useThis = false;

				// present solution
				// alert(useThis)
				if (useThis) {
					// Bug fix April 3 2009
					// if there were more than two pivots ion a row
					// and it used an earlier one for which the pivot was not 1
					// then it reported the incorrect solution
					// fix: divide by the pivot in all cases just in case...
					// implemented in the next two lines
					if (fractionMode || integerMode)
						theStr = toFrac(
							roundSigDig(
								theTableau[theRowx][numCols] / theTableau[theRowx][j],
								15
							),
							maxDenom,
							tol
						);
					else
						theStr = roundSigDig(
							theTableau[theRowx][numCols] / theTableau[theRowx][j],
							numSigDigs
						).toString();
				} else theStr = "0";

				if (j < numVariables) theStr += ", ";

				document.theSpreadsheet.expr.value += theStr;

				//				alert("starred row is row #" + theRowx + "column is "+j)
			} // if a pivot there
			else {
				theStr = "0";

				if (j < numVariables) theStr += ", ";
				document.theSpreadsheet.expr.value += theStr;
			}
		} // j
	} // end of presentation
}

function displayMatrix(number) {
	var theString = "Tabela #" + TableauNumber + cr;

	if (singular) theString += "undefined";
	else {
		var RowNum = numRows;

		var ColNum = numCols;

		// first round all the results and get the longest resulting string

		var maxLength = 1;

		var x = "",
			i = 0,
			j = 0,
			k = 0;

		var xLen = 0;

		// ok to here

		// prepare the stringmatrix if integer mode:

		if (integerMode)
			theStringTableau = makeInteger(theTableau, RowNum, ColNum, true);
		// else, handle fractions & decimals
		else {
			for (i = 1; i <= RowNum; i++) {
				for (j = 1; j <= ColNum; j++) {
					// alert("i = "+i + " j = " + j + "table entry = " + theTableau[i][j]);

					if (fractionMode)
						x = toFrac(roundSigDig(theTableau[i][j], 15), maxDenom, tol);
					else x = roundSigDig(theTableau[i][j], numSigDigs).toString();

					// alert("x = "+x);

					xLen = x.length;

					// alert("xLen =" + xLen);

					if (xLen > maxLength) maxLength = xLen;

					theStringTableau[i][j] = x;
				} // j
			} // i
		} // end else (if not integer mode)

		if (maxLength < 6) maxLength = 6; // more space

		var spaceString = "";

		for (
			i = 0;
			i <= RowNum;
			i++ // was 1
		) {
			for (j = 1; j <= ColNum; j++) {
				if (i == 0) {
					if (j <= numVariables) x = variables[j - 1];
					else if (j == numVariables + numConstraints + 1) {
						x = objectiveName;
						if (!maximization) x = "-" + x;
					} else if (j < ColNum) {
						var mmm = j - numVariables;
						x = "s" + mmm.toString();
					} else if (j == ColNum) x = " ";
				} // end if
				else x = theStringTableau[i][j];

				sp = maxLength - x.length;

				spaceString = "";

				for (k = 0; k <= sp; k++) spaceString += " ";

				theString += x + spaceString;
			} // j

			theString += cr;
		} // i
	} // if not singular

	document.theSpreadsheet.output.value += theString + cr;

	// now convert the strings back to numbers

	return 0;
}

// ******** END OF DISPLAY ROUTINE ***************

function makeArray3(X, Y, Z) {
	var count;

	this.length = X + 1;

	for (var count = 1; count <= X + 1; count++)
		// to allow starting at 1

		this[count] = new makeArray2(Y, Z);
} // makeArray3

function makeArray2(X, Y) {
	var count;

	this.length = X + 1;

	for (var count = 0; count <= X + 1; count++)
		// to allow starting at 1

		this[count] = new makeArray(Y);
} // makeArray2

function makeArray(Y) {
	var count;

	this.length = Y + 1;

	for (var count = 1; count <= Y + 1; count++) this[count] = 0;
} // makeArray

function stripSpaces(InString) {
	OutString = "";

	for (Count = 0; Count < InString.length; Count++) {
		TempChar = InString.substring(Count, Count + 1);

		if (TempChar != " ") OutString = OutString + TempChar;
	}

	return OutString;
}

function stripChar(InString, symbol) {
	OutString = "";

	for (Count = 0; Count < InString.length; Count++) {
		TempChar = InString.substring(Count, Count + 1);

		if (TempChar != symbol) OutString = OutString + TempChar;
	}

	return OutString;
}

function doIt() {
	fractionMode = false;

	integerMode = false;

	var theMode = document.theSpreadsheet.Mode.selectedIndex;

	if (document.theSpreadsheet.Mode.options[theMode].text == "Fraction")
		fractionMode = true;
	else if (document.theSpreadsheet.Mode.options[theMode].text == "Integer")
		integerMode = true;

	var num = doIt.arguments[0];

	//**********

	// Option 1

	if (num == 1) {
		if (okToRoll) {
			TableauNumber = 1;

			document.theSpreadsheet.output.value = ""; // clear answer space

			SetupTableau();

			// alert("tableau is set up");
		} // of okToRoll

		if (okToRoll) {
			theTableau = simplexMethod(theTableau, numRows, numCols);
		}
	} // end of this option

	// Option 2 // preliminary checks
	else if (num == 2) {
		okToRoll = true;

		stepName = "Rounding information";

		var accuracydig = document.theSpreadsheet.acc.value;

		if (accuracydig == "" || !looksLikeANumber(accuracydig)) {
			document.theSpreadsheet.expr.value =
				"O valor de precisão deve estar entre 1-13.";
			okToRoll = false;
		}

		if (okToRoll) {
			var thenum = eval(accuracydig);

			if (thenum < 1 || thenum > 14) {
				document.theSpreadsheet.expr.value =
					"O valor de precisão deve estar entre 1-13.";
				okToRoll = false;
			} else numSigDigs = thenum;

			if (document.theSpreadsheet.input.value == "") {
				document.theSpreadsheet.expr.value =
					"Digite um problema de programação linear na caixa de entrada acima.";
				okToRoll = false;
			}
		} // if okToRoll
	} // end of this option

	// Option 3 (Erase)
	else if (num == 3) {
		document.theSpreadsheet.input.value = "";

		document.theSpreadsheet.output.value = "";

		document.theSpreadsheet.expr.value = "";
	}

	// compute the expression
	else if (num == 4) {
	} // of this option

	//
	else if (num == 5) {
		document.theSpreadsheet.input.value = theSampleLPString;

		if (document.theSpreadsheet.acc.value == "")
			document.theSpreadsheet.acc.value = numSigDigs;

		document.theSpreadsheet.expr.value =
			"Clique em 'Resolver' para ver a solução do problema acima.";

		document.theSpreadsheet.output.value = theInstructionString;
	}

	// Option 6
	else if (num == 6) {
	} // of this option
}
