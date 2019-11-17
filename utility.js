"use strict";

function byte_length(s) {
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

	var text_length = byte_length(val);
	console.log(text_length);

	// text_length = Math.max(text_length, input.attr('placeholder').length);
	// text_length = Math.min(text_length, 32);

	text_length /= 2;
	text_length += 2;
	input.css("width", text_length + "em");
}

