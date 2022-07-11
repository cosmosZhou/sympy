<template>
	<div>
		<select v-if=phrases v-focus name=suggest class='non-arrowed' :style=select_style :size=select_size @keydown=keydown_select @blur=blur>
			<option v-for="phrase in phrases" :value=phrase>{{phrase}}</option>
		</select>
		<input v-focus spellcheck=false ref=input name=module :value=module :size=input_size @keydown=keydown @input=oninput @change=onchange >
	</div>
</template>

<script>
function getTextWidth(str) {
	let result = 0;
	let div = document.createElement("div");
	div.setAttribute('class', "Consolas");
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

console.log('importing newInput.vue');
export default {
	props : [ 'module'],
	
	created(){
	},
	
	updated(){
	},
	
	data(){
		return {
			phrases: null,
			start: -1,
		};
	},
	
	computed: {
		input_size(){
			return this.module.length;
		},
		
		select_size(){
			return Math.min(this.phrases.length, 10);
		},
		
		char_width(){
			return getTextWidth("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") / 52;	
		},
		
		select_style(){
			var offset = this.start * this.char_width;
			return `transform: translate(${offset}px, 20px)`;
		},
		
		editor(){
			return this.$refs.input;
		},
		
		input(){
			return this.$refs.input;
		},
	},
	
	methods: {
		async complete(hint, prefix, start){
			var phrases = await form_post(`php/request/${hint}.php`, { prefix: prefix });
			if (!phrases.length) {
				return;
			}
			
			var input = this.input;
			var value = input.value;
			console.log("before assignment: value = ", value);
			console.log("before assignment: module = ", this.module);
			
			if (phrases.length == 1) {
				var [phrase] = phrases;
				
				var start1 = input.selectionStart;							
				var start0 = start1;
				start0 = start1 + prefix.search(/\w*$/) - prefix.length;						
				value = value.slice(0, start0) + phrase + value.slice(start1);
				console.log("after assignment:", value);
				
				input.value = value;
				this.set_module(value);
				
				var selectionStart = start0 + phrase.length;
				input.selectionStart = selectionStart;
				input.selectionEnd = selectionStart;							
			}
			else{
				this.phrases = phrases;
				this.start = start + 1;
			}
		},
		
		keydown(event){
			var self = event.target; 
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
					var start = self.selectionStart;
					var text = text.slice(0, start);

					var prefix = text.match(/([\w.]+)$/)[1] + key;

					console.log(`perform code suggestion on ${prefix}`);
					this.complete("hint", prefix, start);
					break;
				case '.':
					var start = self.selectionStart;
					var text = text.slice(0, start);

					var prefix = text.match(/([\w.]+)$/)[1] + key;

					console.log(`perform code suggestion on ${prefix}`);
					this.complete("suggest", prefix, start);
					break;
				case 'ArrowDown':
					var cm = this.$parent.newApply.editor;
					cm.focus();

					var linesToMove = cm.getCursor().line;
					for (let i = 0; i < linesToMove; ++i) {
						cm.moveV(-1, "line");
					}
					break;
				case 'F3':
					console.log("F3 is pressed");
					find_and_jump(event);
					break;
					
				case 's':
					if (event.ctrlKey){
						event.preventDefault();
						saveDocument();
					}
					break;						
					
				default:
					break;
			}
			
		},	
		
		blur(event){
			this.phrases = null;	
		},
		
		
		keydown_select(event){
			var self = event.target;
			switch (event.key) {
			case 'Enter':
				var phrase = self.options[self.selectedIndex].value;

				var input = self.nextElementSibling;
				//var selectionStart = input.selectionStart;
				var selectionStart = this.start;
				var value = input.value;
				var pos;
				if (value[selectionStart - 1] == '.'){
					pos = selectionStart;
				}
				else{
					pos = value.slice(0, selectionStart).search(/\w+$/);
				}
				
				value = value.slice(0, pos) + phrase + value.slice(selectionStart);
				input.value = value;
				this.set_module(value);
				
				this.phrases = null;
				
				selectionStart += phrase.length;
				break;
			case 'Escape':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;
				
				this.phrases = null;					
				break;
			case 'Backspace':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;

				var value = input.value;
				value = text.slice(0, selectionStart - 1) + text.slice(selectionStart);
				input.value = value;
				this.set_module(value);

				this.phrases = null;
				--selectionStart;
				break;
			case 'Delete':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;
				var value = input.value;
				value = text.slice(0, selectionStart) + text.slice(selectionStart + 1);
				input.value = value;
				this.set_module(value);
				break;
			case 'ArrowLeft':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;

				// console.log("selectionStart = " + selectionStart);
				this.phrases = null;
				
				--selectionStart;
				break;
			case 'ArrowRight':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;

				this.phrases = null;
				
				++selectionStart;
				break;
			default:
				return;
			}
			
			this.$nextTick(()=>{
				var input = this.input;
				input.focus();
				input.selectionStart = selectionStart;
				input.selectionEnd = selectionStart;
			});
		},
		
		oninput(event){
			this.set_module(event.target.value);
		},
		
		onchange(event){
			document.title = event.target.value;	
		},
		
		set_module(module){
			setAttribute(this, 'module', module);
		},
	},
	
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
				el.focus();
		    },
		},
	},
};
</script>

<style>

select {	
	width: auto;	
	z-index: 10;
	position: absolute;
	outline: none;
}

.non-arrowed {
	-webkit-appearance: none;
	-moz-appearance: none;
	border: 0;
	font-size: inherit;
}

</style>