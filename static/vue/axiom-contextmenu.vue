<template>
	<ul class=contextmenu tabindex=2
		:style="'left:%spx; top:%spx'.format(left, top)" @blur=blur
		@keydown=keydown>
		<li class=select @mouseover=mouseover @mouseout=mouseout @click=clickRename><u>R</u>ename</li>
		<li class=select @mouseover=mouseover @mouseout=mouseout @click=clickDelete><u>D</u>elete</li>
		<li class=expand @mouseover=mouseover @mouseout=mouseout @click=clickMoveTo>
			<u>M</u>ove to ...			
		</li>
		<li class=select @mouseover=mouseover @mouseout=mouseout @click=clickOpenInNewTab>Open
			in new <u>t</u>ab</li>
		<li class=select @mouseover=mouseover @mouseout=mouseout
			@click=clickOpenInNewWindow>Open in new <u>w</u>indow</li>
		<li class=select @mouseover=mouseover @mouseout=mouseout @click=clickProperty><u>P</u>roperty</li>
	</ul>
</template>

<script>	
	console.log('importing axiom-contextmenu.vue');
	module.exports = {
		data(){
			return {
				focusedIndex: -1,	
			};
		},
		
		props : [ 'left', 'top' ],
		
		computed:{
			numOfLi(){
				return this.$el.children.length;
			}
		},
		
		watch: {
			focusedIndex(newIndex, oldIndex){
				var children = this.$el.children;
				//console.log("oldIndex = " + oldIndex);
				//console.log("newIndex = " + newIndex);				
				
				if (newIndex >= 0)
					children[newIndex].style.background = '#ccc';
				
				if (oldIndex >= 0)
					children[oldIndex].style.background = null;
				
			}
		},
		
		methods : {		
			click(event, args){
				console.log(event);				
				console.log(args);
			},
		
			clickProperty(event){
			},
			
			clickDelete(event){
				console.log("clickDelete(event){");
				var parent = this.$parent;
				var indexFocused = parent.focusedIndex;
				this.focusedIndex = -1;
				
				var self = parent.$children[indexFocused];
				self.remove();
				parent.remove(indexFocused);				
			},
			
			clickMoveTo(event){
				parent = this.$parent;				
				parent.left = -1;
				
				var href = location.href;
				var subFolder = href.match(/\/axiom.php(\/.*)\/(\w+)\/*$/)[2];
				
				var indexFocused = parent.focusedIndex;
				
				promise(()=>{
					
					var packageSelector = null;
					for (let child of parent.$children){
						if (child.$el.className == 'packageSelector-wrapper'){
							packageSelector = child;
							break;
						}
					}
					
					packageSelector.focus(subFolder);
				});
			},
			
			clickRename(event){				
				var parent = this.$parent;
				var icon = parent.$children[parent.focusedIndex];
				console.log('icon = ');
				console.log(icon);				
				
				parent.focusedIndex = -1;
				icon = icon.$children[0];
				icon.rename();
			},
			
			clickOpenInNewTab(event){				
				window.open(this.get_href());
			},
			
			clickOpenInNewWindow: function(event){				
//window.open(location.href + theorem, "_blank", "toolbar=yes,top=500,left=500,width=400,height=400");
				window.open(this.get_href(), "_blank", "toolbar=yes");
			},
			
			get_href: function(){
				var icon = this.$parent.$children[this.$parent.focusedIndex];

				var theorem = icon.$el.lastChild.textContent.trim();
				var href = location.href;
				if (!href.endsWith('/')){
					href += '/';
				}
				
				console.log("theorem = " + theorem);
				this.$parent.focusedIndex = -1;
				return href + theorem;				
			},
			
			blur(event){
				if (this.$parent.left >= 0)
					this.$parent.focusedIndex = -1;
			},
			
			keydown(event){
				console.log("keydown(event){");
				var key = event.key;
				switch(key){
				case 'ArrowDown':
					++this.focusedIndex;
					if (this.focusedIndex == this.numOfLi){
						this.focusedIndex = -1;
					}
					break;
					
				case 'ArrowUp':					
					if (this.focusedIndex < 0){
						this.focusedIndex = this.numOfLi;
					}
					
					--this.focusedIndex;
					break;
				case 'Enter':
					this.$el.children[this.focusedIndex].click();
					break;
				default:
					if (key.length == 1){
						var re = RegExp(`<u>${key}</u>`, "i");
					
						for (var i = 0; i < this.numOfLi; ++i){
							if (re.exec(this.$el.children[i].innerHTML)){
								this.focusedIndex = i;
								break;
							}
						}
					}
				}
			},
			
			mouseover(event){							
				var li = event.target;				
				this.focusedIndex = this.$el.children.indexOf(li);
			},
			
			mouseout(event){
				this.focusedIndex = -1;
			},
			
		},
	}
</script>

<style>
.contextmenu {
	margin: 0;
	background: #fff;
	z-index: 3000;
	position: absolute;
	list-style-type: none;
	padding: 5px 0;
	border-radius: 4px;
	font-size: 12px;
	font-weight: 400;
	color: #333;
	box-shadow: 2px 2px 3px 0 rgba(0, 0, 0, 0.3);
}

.contextmenu li.select {
	margin: 0;
	padding: 7px 16px;
	cursor: pointer;
}

.contextmenu li.expand {
	margin: 0;
	padding: 7px 1px 7px 16px;
	cursor: pointer;
}

ul:focus {
	outline: none;
}
</style>