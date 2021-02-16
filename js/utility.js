"use strict";

function strlen(s) {
	var length = 0;
	for (let i = 0; i < s.length; i++) {
		var code = s.charCodeAt(i)
		if (code < 128 || code == 0x2002)
			length += 1;
		else
			length += 2;
	}
	return length;
}

function changeInputlength(input) {
	var val = input.val();
	console.log(val);

	var text_length = strlen(val);
	console.log(text_length);

	// text_length = Math.max(text_length, input.attr('placeholder').length);
	// text_length = Math.min(text_length, 32);

	text_length /= 2;
	text_length += 2;
	input.css("width", text_length + "em");
}

function toggle_expansion_button() {
	$('button').click(function() {
		var div = $(this)[0].nextElementSibling;
		if ($(this).text() == '>>>>') {

			div.style.display = 'block';

			$(this).text('<<<<');

		} else {

			div.style.display = null;

			$(this).text('>>>>');

		}
	});
}

function click_first_expansion_button() {
	var first_button = document.querySelector("button");
	first_button.click();
}

function click_all_expansion_buttons() {
	var buttons = document.querySelectorAll("button");
	for (let button of buttons) {
		button.click();
	}
}

window.onload = function() {
	var currentFunctionKey = null;
	// currentFunctionKey = window.currentFunctionKey;
	// console.log('register: function (MainKey, value, func)');
	document.onkeyup = function(event) {
		console.log('onkeyup');
		var key = event.key;
		console.log('key = ' + key);
		if (key == currentFunctionKey)
			currentFunctionKey = null;
	}

	document.onkeydown = function(event) {
		var key = event.key;
		console.log('onkeydown');
		console.log('key = ' + key);

		console.log('currentFunctionKey = ' + currentFunctionKey);

		if (currentFunctionKey == null) {
			currentFunctionKey = key;
			return;
		}

		switch (currentFunctionKey) {
			case 'Alt':
				switch (key) {
					case 'c':
						console.log("M-c");
						var checkbox = $('input[type=checkbox][name=CaseSensitive]')[0];
						checkbox.checked = !checkbox.checked;
						break;
					case 'd':
						console.log("M-d");
						break;
					case 'l':
						console.log("M-l");
						break;
					case 'r':
						console.log("M-r");
						break;
					case 't':
						console.log("M-t");
						break;
					case 'w':
						console.log("M-w");
						var checkbox = $('input[type=checkbox][name=WholeWord]')[0];
						checkbox.checked = !checkbox.checked;						
						break;
					case 'x':
						console.log("M-x");						
						var checkbox = $('input[type=checkbox][name=RegularExpression]')[0];
						checkbox.checked = !checkbox.checked;
						break;
					case '\r':
					case '\n':
						console.log("Alt + Enter");
						break;
				}
				break;
			case 'Control':
				switch (key) {
					case 'd':
						console.log("C-d");
						break;
					case 'l':
						console.log("C-l");
						break;
					case 'r':
						console.log("C-r");
						break;
					case 't':
						console.log("C-t");
						break;
					case 'Home':
						$("input[type=text]")[0].focus();
						console.log("C-Home");
						break;
					case 'Insert':
						console.log("C-Insert");
						break;
					case 'Enter':
						console.log("C-Enter");
						//submit();
						break;

				}
				break;

			case 'Shift':
				switch (key) {
					case 'Enter':
						console.log("Shift + Enter");
						//submit();
						break;
				}
				break;
			default:
				switch (key) {
					case 40: // DownArrow
						console.log("DownArrow");
						break;
					case 38: // UPArrow
						console.log("UPArrow");
						break;
				}
				break;
		}
	}
}
