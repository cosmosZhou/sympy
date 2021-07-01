
function fromTextArea(textarea, theme) {

	var _extraKeys = extraKeys();
	Object.assign(_extraKeys, {
		'Ctrl-O': function(cm) {
			console.log("'Ctrl-O' is pressed!");
			var module = form.querySelector('a').href;
			module = module.match(/=([\w.]+)/)[1];
			location.href = "/sympy/php/new.php?module=" + module;
		},

		'Ctrl-S': function(cm) {
			console.log("'Ctrl-S' is pressed!");
		},

		'Ctrl-F11': function(cm) {
			form.submit();
		},

		'Shift-Alt-W': function(cm) {
			console.log('Shift-Alt-W');
			var index = location.href.lastIndexOf('/') + 1;
			location.href = location.href.substring(0, index);
		},
	});


	return CodeMirror.fromTextArea(textarea, {
		mode: {
			name: "python",
			singleLineStringErrors: false
		},

		theme: theme || 'function',

		indentUnit: 4,

		matchBrackets: true,

		scrollbarStyle: null,

		extraKeys: _extraKeys,

		hintOptions: { hint: hint }
		//equivalently:		
		//CodeMirror.registerHelper("hint", "python", hint);
	});
}

function fromTextAreaOfProve() {
	var proveEditors = []
	for (let proveCode of form.querySelectorAll("textarea[name='prove[]']")) {
		proveEditors.push(fromTextArea(proveCode));
	}
	return proveEditors;
}

var app = new Vue({
	el: '#root',

	computed: {
		error() {
			for (let log of this.logs) {
				if (typeof log == 'string')
					continue;
				return log;
			}
		},
	},

	methods: {
		click(event) {
			if (this.error.prove) {
				var line = this.error.line;
				var sum = 0;
				console.log("proveEditors.length = " + proveEditors.length);
				for (let cm of proveEditors) {
					var _sum = sum;
					sum += cm.lineCount();
					if (sum > line) {
						cm.focus();
						cm.setCursor(line - _sum, 0);
						break;
					}
				}
			}
			else if (this.error.apply) {
				console.log(this.error);
				var line = this.error.line;

				if (this.error.module) {
					var href = location.href;
					href = href.match(/(.+\/axiom.php\/).+/)[1];
					href += this.error.module;
					href += `?apply=${line}`;
					window.open(href);
				}
				else{
					open_apply(line);
				}
			}
		},
	},
	data: data,
});

if (sql) {
	execute_sql(sql);
}


var proveEditors = fromTextAreaOfProve();

proveEditors[0].focus();

var editorForApply = null;
for (let i = 0; i < proveEditors.length; ++i) {
	proveEditors[i].addKeyMap({
		Left(cm) {
			cm.moveH(-1, "char");
			if (cm.getCursor().hitSide) {
				if (i == 0) {
					cm = editorForApply;
				}
				else {
					cm = proveEditors[i - 1];
				}

				cm.focus();
				CodeMirror.commands.goDocEnd(cm);
			}
		},

		Right(cm) {
			cm.moveH(1, "char");
			if (cm.getCursor().hitSide) {
				cm = proveEditors[i + 1];
				cm.focus();
				CodeMirror.commands.goDocStart(cm);
			}
		},

		Down(cm) {
			var cursor = cm.getCursor();
			if (cursor.line + 1 < cm.lineCount())
				return cm.moveV(1, "line");

			cm = proveEditors[i + 1];
			cm.focus();

			if (cursor.ch == 0) {
				var linesToMove = cm.getCursor().line;
				for (let i = 0; i < linesToMove; ++i) {
					cm.moveV(-1, "line");
				}
			}
			else
				cm.setCursor(0, cursor.ch);
		},

		PageDown(cm) {
			var cursor = cm.getCursor();
			if (cursor.line + 18 < cm.lineCount())
				return cm.moveV(1, "page");

			cm = proveEditors[i + 1];
			cm.focus();

			if (cursor.ch == 0) {
				var linesToMove = cm.getCursor().line;
				for (let i = 0; i < linesToMove; ++i) {
					cm.moveV(-1, "line");
				}
			}
			else
				cm.setCursor(0, cursor.ch);
		},

		Up(cm) {
			var cursor = cm.getCursor();
			if (cursor.line > 0)
				return cm.moveV(-1, "line");
			if (i == 0) {
				cm = editorForApply;
			}
			else {
				cm = proveEditors[i - 1];
			}

			cm.focus();
			if (cursor.ch == 0 || i == 0) {
				var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
				for (let i = 0; i < linesToMove; ++i) {
					cm.moveV(1, "line");
				}
			} else
				cm.setCursor(cm.lineCount() - 1, cursor.ch);
		},

		"Ctrl-Enter": cm => {
			CodeMirror.commands.newlineAndIndent(cm);			
		},
		
		PageUp(cm) {
			var cursor = cm.getCursor();
			if (cursor.line >= 18)
				return cm.moveV(-1, "page");
			if (i == 0) {
				cm = editorForApply;
			}
			else {
				cm = proveEditors[i - 1];
			}

			cm.focus();
			if (cursor.ch == 0 || i == 0) {
				var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
				for (let i = 0; i < linesToMove; ++i) {
					cm.moveV(1, "line");
				}
			}
			else
				cm.setCursor(cm.lineCount() - 1, cursor.ch);
		},

		F3,

		'Ctrl-F3': cm => F3(cm, true),

		'Ctrl-End': cm => {
			cm = proveEditors.back();
			cm.focus();
			return cm.extendSelection(CodeMirror.Pos(cm.lastLine()));
		},

		'Ctrl-Home': cm => {
			cm = editorForApply
			if (cm == null) {
				cm = proveEditors[0];
			}
			cm.focus();
			return cm.extendSelection(CodeMirror.Pos(cm.firstLine(), 0));
		},
	});
}

function open_apply(arg) {
	var textarea = form.querySelector('textarea[name=apply]');
	if (textarea) {
		editorForApply.focus();
	}
	else {
		var module = location.href.match(/axiom\.php\/([\w\/]+)/)[1].replace(/\//g, '.');

		request_post("/sympy/php/request.php", { apply: module }).done(code => {
			//console.log('code = ' + code);

			var textarea = document.createElement('textarea');
			textarea.name = 'apply';
			textarea.value = code;

			form.insertBefore(textarea, form.querySelector("textarea[name='prove[]']"));

			editorForApply = fromTextArea(textarea, 'eclipse');
			editorForApply.focus();

			editorForApply.addKeyMap({
				Down(cm) {
					var cursor = cm.getCursor();
					if (cursor.line + 1 < cm.lineCount())
						return cm.moveV(1, "line");

					cm = proveEditors[0];
					cm.focus();
					if (cursor.ch == 0) {
						var linesToMove = cm.getCursor().line;
						for (let i = 0; i < linesToMove; ++i) {
							cm.moveV(-1, "line");
						}
					}
					else
						cm.setCursor(0, cursor.ch);
				},

				Right(cm) {
					cm.moveH(1, "char");
					if (cm.getCursor().hitSide) {
						cm = proveEditors[0];
						cm.focus();
						CodeMirror.commands.goDocStart(cm);
					}
				},

				PageDown(cm) {
					var cursor = cm.getCursor();
					if (cursor.line + 18 < cm.lineCount())
						return cm.moveV(1, "page");

					cm = proveEditors[0];
					cm.focus();
					if (cursor.ch == 0) {
						var linesToMove = cm.getCursor().line;
						for (let i = 0; i < linesToMove; ++i) {
							cm.moveV(-1, "line");
						}
					} else
						cm.setCursor(0, cursor.ch);
				},

				F3,

				'Ctrl-F3': cm => F3(cm, true),

				'Ctrl-End': cm => {
					cm = proveEditors.back();
					cm.focus();
					return cm.extendSelection(CodeMirror.Pos(cm.lastLine()));
				},
			});

			if (arg) {
				if (typeof arg === 'number' || arg.match(/^\d+/)) {
					editorForApply.setCursor(parseInt(arg), 4);
				}
				else {
					var regex = eval(`/((?:    )*def ${arg})\\([^()]+\\):\\s*$/`);

					var size = editorForApply.lineCount();
					for (var index = 0; index < size; ++index) {
						var line = editorForApply.getLine(index);
						//console.log(line);

						var m = line.match(regex);
						if (m) {
							editorForApply.setCursor(index, m[1].length - arg.length / 2);
							break;
						}
					}
				}
			}

		}).fail(fail);
	}
}

function locate_definition(cm, index, symbol) {
	var regex = eval(`/(?:    )*from axiom\\.(.+) import ${symbol}\\b/`);

	for (; index >= 0; --index) {
		var line = cm.getLine(index);
		console.log(line);

		var m = line.match(regex);
		if (m) {
			return m[1];
		}
	}
}

function F3(cm, refresh) {
	var cursor = cm.getCursor();
	console.log("cursor.ch = " + cursor.ch);

	var text = cm.getLine(cursor.line);

	var selectionStart = cursor.ch;
	console.log("selectionStart = " + selectionStart);

	for (; selectionStart < text.length; ++selectionStart) {
		var char = text[selectionStart];
		if (char >= 'a' && char <= 'z' ||
			char >= 'A' && char <= 'Z' ||
			char == '_' ||
			char >= '0' && char <= '9') {
			continue;
		}
		else {
			break;
		}
	}

	var textForFocus = text.slice(0, selectionStart);
	var m = textForFocus.match(/(\w+)(?:\.\w+)*$/);
	var module = m[0];
	console.log('module = ' + module);
	switch (module) {
		case 'apply':
			open_apply();
			break;

		case 'prove':
			break;

		default:
			var m = module.match(/(.+)\.apply$/);
			if (m) {
				module = m[1];
				var apply = true;
			}
			else {
				var apply = false;
			}

			m = module.match(/^axiom\.(.+)/);
			if (m) {
				module = m[1];
			}

			var symbol = null;

			if (module.indexOf('.') < 0) {
				switch (module) {
					case 'algebra':
					case 'calculus':
					case 'discrete':
					case 'geometry':
					case 'keras':
					case 'sets':
					case 'stats':
						break;
					default:
						var symbol = module;
						module = locate_definition(cm, cursor.line, symbol);
						if (module == null)
							return;
				}
			}
			else {
				m = module.match(/^(\w+)\.(.+)/);
				switch (m[1]) {
					case 'algebra':
					case 'calculus':
					case 'discrete':
					case 'geometry':
					case 'keras':
					case 'sets':
					case 'stats':
						break;
					default:
						return;
				}
			}

			var href = "/sympy/axiom.php/%s".format(module.replace(/\./g, '/'));

			if (apply)
				href += "?apply=true";
			else if (symbol)
				href += `?apply=${symbol}`;

			if (refresh)
				location.href = href;
			else
				window.open(href);

			break;
	}
}

function detect_cycle(module) {
	console.log("function detect_cycle(module)");
	//	underline_all_theorems();

	console.log('module = ' + module);

	request_post("/sympy/php/request.php", { detect: module }).done(theorem => {
		console.log('theorem = ' + theorem);

		//theorem = theorem.replace(/\./g, '/');		

		console.log('theorem = ' + theorem);

		for (let editor of proveEditors) {
			editor.eachLine(line => {
				var text = line.text;
				var selectionStart = text.indexOf(theorem);
				if (selectionStart >= 0) {
					console.log(text);
					var lineNo = line.lineNo();

					editor.setCursor(lineNo, selectionStart);
					editor.addSelection({ line: lineNo, ch: selectionStart }, { line: lineNo, ch: selectionStart + theorem.length });
					editor.focus();
				}
			});
		}
	}).fail(fail);
}


detect_cycle(data.module);

if (apply)
	open_apply(apply);

//http://codemirror.net/doc/manual.html