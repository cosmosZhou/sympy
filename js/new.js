function remove(child) {
	try {
		child.remove();
	}
	catch (err) {
		// console.log(err.message);
	}
}

function getTextWidth(str) {
	let result = 0;
	let div = document.createElement("div");
	div.setAttribute('class', "Consolas");
	// div.style.fontStyle = 'normal';
	// div.style.fontSize = "1em";
	// div.style.fontWeight = "normal";
	// div.style.fontFamily = "Consolas";

	div.style.backgroundColor = 'inherit';
	div.style.borderStyle = 'none';
	div.style.outline = 'none';

	div.style.opacity = 0;
	div.style.position = "absolute";
	div.style.whiteSpace = "nowrap";

	div.innerText = str;
	document.body.append(div);
	result = div.getBoundingClientRect().width;
	div.remove();
	return result;
}

function onkeydown_select(self, event) {
	switch (event.key) {
		case 'Enter':
			var phrase = $(self).find("option:selected").text();

			var input = self.nextElementSibling;
			var selectionStart = input.selectionStart;

			var text = input.value;
			input.value = text.slice(0, selectionStart) + phrase + text.slice(selectionStart);

			remove(self);
			//self.remove();
			input.focus();
			selectionStart += phrase.length;
			break;
		case 'Escape':
			var input = self.nextElementSibling;
			var selectionStart = input.selectionStart;
			remove(self);
			//self.remove();
			input.focus();
			break;
		case 'Backspace':
			var input = self.nextElementSibling;
			var selectionStart = input.selectionStart;

			var text = input.value;
			input.value = text.slice(0, selectionStart - 1) + text.slice(selectionStart);

			remove(self);
			//self.remove();
			input.focus();
			--selectionStart;
			break;
		case 'Delete':
			var input = self.nextElementSibling;
			var selectionStart = input.selectionStart;
			var text = input.value;
			// console.log("text = " + text);
			// console.log("selectionStart = " + selectionStart);
			input.value = text.slice(0, selectionStart) + text.slice(selectionStart + 1);
			break;
		case 'ArrowLeft':
			var input = self.nextElementSibling;
			var selectionStart = input.selectionStart;

			// console.log("selectionStart = " + selectionStart);
			remove(self);
			//self.remove();
			input.focus();
			--selectionStart;
			break;
		case 'ArrowRight':
			var input = self.nextElementSibling;
			var selectionStart = input.selectionStart;

			remove(self);
			//self.remove();
			input.focus();
			++selectionStart;
			break;
		default:
			return;
	}

	input.selectionStart = selectionStart;
	input.selectionEnd = selectionStart;
}

function create_suggest_selector(phrases, start) {
	//globals definition go here:
	var char_width = getTextWidth("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") / 52;

	var select = document.createElement('select');
	select.name = 'suggest';
	select.setAttribute('class', 'non-arrowed');
	var maxLength = 0;

	if (phrases.length == 1) {
		phrases.push("");
	}

	for (let phrase of phrases) {
		select.appendChild(new Option(phrase, phrase));
		if (phrase.length > maxLength) {
			maxLength = phrase.length;
		}
	}

	start += 1;
	select.style.width = 'auto';
	select.style.position = 'absolute';
	select.style.transform = 'translate(%spx, 20px)'.format(start * char_width);
	select.style.zIndex = 10;
	select.style.outline = 'none';

	select.size = Math.min(phrases.length, 10);

	select.setAttribute('onkeydown', "onkeydown_select(this, event)");
	select.setAttribute('onblur', "onblur_select(this)");
	select.options.selectedIndex = 0;

	return select;
}

function onblur_select(self) {
	console.log("in function onblur_select(self)");

	var input = self.nextElementSibling;
	var selectionStart = input.selectionStart;

	remove(self);
	//self.remove();
	input.focus();

	input.selectionStart = selectionStart;
	input.selectionEnd = selectionStart;
}

function onkeydown_input(self, event) {
	//console.log("in function onkeydown_input(self, event)");
	var text = self.value;

	if (self.size <= text.length) {
		self.size = text.length * 1.5;
	}

	var key = event.key;
	switch (key) {
		case '/':
			if (!event.altKey)
				break;
			key = '';
		case '.':
			var start = self.selectionStart;
			var text = text.slice(0, start);

			var prefix = text.match(/([\w.]+)$/)[1] + key;

			console.log(`perform code suggestion on ${prefix}`);

			request_post("/sympy/php/request.php", { suggest: prefix }).done(phrases => {
				if (phrases.length) {
					// console.log('phrase = ' + phrases);

					var select = create_suggest_selector(phrases, start);
					self.parentElement.insertBefore(select, self);
					select.focus();
				}
			}).fail(fail);

			break;
		case 'ArrowDown':
			cm = applyEditor;
			cm.focus();

			var linesToMove = cm.getCursor().line;
			for (let i = 0; i < linesToMove; ++i) {
				cm.moveV(-1, "line");
			}

		default:
			break;
	}
}

$('input').focus();

_extraKeys = extraKeys();
Object.assign(_extraKeys, {
	'Ctrl-S': function(cm) {
		console.log("'Ctrl-S' is pressed!");
		var module = $('input').val();
		console.log("module = " + module);
		module = module.replace(/\./g, '/');
		console.log("module = " + module);

		form.action = "/sympy/axiom.php/" + module;
		console.log("form.action = " + form.action);

		console.log("save the content now");
		form.submit();
	},

	'Down': function(cm) {
		var cursor = cm.getCursor();
		if (cursor.line + 1 < cm.lineCount())
			return cm.moveV(1, "line");

		cm = proveEditor;
		cm.focus();

		if (cursor.ch == 0) {
			var linesToMove = cm.getCursor().line;
			for (let i = 0; i < linesToMove; ++i) {
				cm.moveV(-1, "line");
			}
		}
		else
			cm.setCursor(0, cursor.ch - 4);
	},

	'Up': function(cm) {
		var cursor = cm.getCursor();
		if (cursor.line > 0)
			return cm.moveV(-1, "line");

		input = document.querySelector('input[name=module]');

		input.focus();
		if (cursor.ch != 0) {
			input.selectioinStart = cursor.ch;
			input.selectioinEnd = cursor.ch;
		}

	},
});

var applyEditor = CodeMirror.fromTextArea(document.getElementById("apply"), {
	mode: {
		name: "python",
		singleLineStringErrors: false
	},

	theme: 'eclipse',

	//lineNumbers: true,
	indentUnit: 4,
	matchBrackets: true,

	scrollbarStyle: null,

	extraKeys: _extraKeys,

	hintOptions: { hint: hint },

});

_extraKeys = extraKeys();
Object.assign(_extraKeys, {
	'Ctrl-S': function(cm) {
		console.log("'Ctrl-S' is pressed!");
		var module = $('input').val();
		console.log("module = " + module);
		module = module.replace(/\./g, '/');
		console.log("module = " + module);

		form.action = "/sympy/axiom.php/" + module;
		console.log("form.action = " + form.action);

		console.log("save the content now");
		form.submit();
	},

	'Up': function(cm) {
		var cursor = cm.getCursor();
		if (cursor.line > 0)
			return cm.moveV(-1, "line");

		cm = applyEditor;

		cm.focus();
		if (cursor.ch == 0) {
			var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
			for (let i = 0; i < linesToMove; ++i) {
				cm.moveV(1, "line");
			}
		} else
			cm.setCursor(cm.lineCount() - 1, cursor.ch + 4);
	},

});

var proveEditor = CodeMirror.fromTextArea(document.getElementById("prove"), {
	mode: {
		name: "python",
		singleLineStringErrors: false
	},

	theme: 'function',
	indentUnit: 4,
	matchBrackets: true,

	scrollbarStyle: null,

	extraKeys: _extraKeys,

	hintOptions: { hint: hint },

});

//     http://codemirror.net/doc/manual.html