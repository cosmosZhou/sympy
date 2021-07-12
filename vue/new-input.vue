<template>
	<div>
		<select v-if=phrases name=suggest class='non-arrowed' 
		:style=select_style :size=select_size
		@keydown=keydown_select>
			<option v-for="phrase in phrases" :value=phrase>{{phrase}}</option>
		</select>
		<input spellcheck=false name=module v-model=module :size=input_size @keydown=keydown />
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

	console.log('importing new-input.vue');
	module.exports = {
		props : [ 'module'],
		
		created(){
            promise(()=>{
            	this.$el.querySelector('input').focus();
            });
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
				return strlen(this.module);
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
		},
		
		methods: {
			complete(hint, prefix, start){
				request_post(`/sympy/php/request/${hint}.php`, { prefix: prefix }).done(phrases => {
					if (phrases.length) {
						if (phrases.length == 1) {
							var [phrase] = phrases;
							var input = this.$el.querySelector('input');
							var start1 = input.selectionStart;							
							var start0 = start1 - prefix.length + prefix.search(/\w*$/);
							var text = input.value;
							
							this.module = input.value = text.slice(0, start0) + phrase + text.slice(start1);
							var selectionStart = start0 + phrase.length;
							input.selectionStart = selectionStart;
							input.selectionEnd = selectionStart;							
						}
						else{
							this.phrases = phrases;
							this.start = start + 1;
							
				            promise(()=>{
				            	this.$el.querySelector('select').focus();
				            });
						}
					}
				}).fail(fail);				
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
						cm = this.$parent.$refs.apply.editor;
						cm.focus();

						var linesToMove = cm.getCursor().line;
						for (let i = 0; i < linesToMove; ++i) {
							cm.moveV(-1, "line");
						}

					default:
						break;
				}
				
			},	
			
			keydown_select(event){
				var self = event.target;
				switch (event.key) {
				case 'Enter':
					var phrase = $(self).find("option:selected").text();

					var input = self.nextElementSibling;
					var selectionStart = input.selectionStart;

					var text = input.value;
					if (text[selectionStart - 1] == '.'){
						this.module = input.value = text.slice(0, selectionStart) + phrase + text.slice(selectionStart);	
					}
					else{
						var pos = text.slice(0, selectionStart).search(/\w+$/); 
						this.module = input.value = text.slice(0, pos) + phrase + text.slice(selectionStart);
					}					

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

					var text = input.value;
					this.module = input.value = text.slice(0, selectionStart - 1) + text.slice(selectionStart);

					this.phrases = null;
					--selectionStart;
					break;
				case 'Delete':
					var input = self.nextElementSibling;
					var selectionStart = input.selectionStart;
					var text = input.value;
					// console.log("text = " + text);
					// console.log("selectionStart = " + selectionStart);
					this.module = input.value = text.slice(0, selectionStart) + text.slice(selectionStart + 1);
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
					var input = this.$el.querySelector('input');
					input.focus();
					input.selectionStart = selectionStart;
					input.selectionEnd = selectionStart;
				});
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