# lean-chat: user guide
An OpenAI Codex-powered chat interface for translating natural language theorem statements into Lean mathlib. 

<img src="https://user-images.githubusercontent.com/59542043/173930999-66b8d089-f01b-48bd-98d3-c26444a57eb0.png" width="300" />

This interface is very much a prototype, so feel free to open issues describing bugs or UI problems. 

## Setup
Users must provide their own OpenAI API key by setting the environment variable `OPENAI_API_KEY`. We are working on a future version that does not require users to have a key. In the meantime, you can apply for a key [here](https://share.hsforms.com/1GzaACuXwSsmLKPfmphF_1w4sk30?).

Once your environment variable is configured, download this repo using the [leanproject](https://leanprover-community.github.io/leanproject.html) command. Open the file `playground.lean`, and hover your cursor over `#html` on line 3 to access the chat widget. 

## Usage 
To get started, simply write a theorem statement in LateX inside the dialogue box. In a few seconds, Codex will return its best attempting at formalizing the natural language. If the Codex output looks good, hit `paste` to copy the code into `playground.lean`. 

If Codex made a mistake, you can give the system a suggestion for what to fix by entering more text into the dialogue box. See below for an example of a multi-turn conversation with Codex that results in a correct formal statement. 

<img src="https://user-images.githubusercontent.com/59542043/173934790-b8713eb8-1e16-4bbd-a18b-c58c2cbeb743.png" width="400"/>
