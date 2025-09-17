# Announcement

I am delighted to have been selected for the award of a grant from Renaissance Philanthropy from the [AI for Mathematics Fund](https://www.renaissancephilanthropy.org/ai-for-math-fund-projects) managed by Renaissance Philanthropy in partnership with founding donor XTX Markets.

## Introduction

AI/ML systems, especially Foundation Models, are now capable of mathematical reasoning at high levels, with models such as Gemini-2.5-pro and OpenAI’s o3 and GPT-5 solving problems at levels comparable to excellent research students. Yet three related limitations come in the way of their more widespread adoption - their accuracy, scalability and autonomy. Indeed to allow scalable and/or autonomous use, it is not sufficient to have a reasonably high accuracy as a single error makes a chain of mathematical reasoning invalid. 

It is widely believed that the best way to overcome these limitations is to integrate with Interactive Theorem Provers, with the Lean Theorem Prover being the most promising choice.

Our goal in the project LeanAide is twofold:

1. **Develop Autoformalization tools for Lean users:** These tools will assist in formalizing and discovering mathematical concepts and software within the Lean Prover environment.  They will be deeply integrated into Lean's syntax and workflow to provide seamless assistance, even if imperfect.  

2. **Develop tools for mathematicians (non-Lean experts):**  These tools will provide a user-friendly, *no code*, (browser-based) interface for mathematical research, leveraging Lean in the background to complement Large Language Models (LLMs) by ensuring correctness and organizing mathematical knowledge in a modular fashion.  This will allow mathematicians to benefit from capabilities of Lean and LLMs without needing direct expertise in either.

Lean experts working on mathematical discovery can use the both components together, completing that are needed for the verification but which the system failed to generate.

We will focus on usability and integration with workflows of working mathematicians and Lean users. We provide Lean users with syntax that can be used within their projects to invoke AI assistance. We are also developing a web interface for use of mathematicians with Lean in the background (or foreground if the user chooses). We will also have a forked version of the Lean server with AI assistance.

## Background, Skills, Implementation

This work will build on both [existing code](https://github.com/siddhartha-gadgil/LeanAide) and experience and skills acquired over the years.

I started my career working in mathematics (with a PhD from Caltech), specifically Topology, Geometric Group theory and related fields and continue to work to some extent with these. I have also been fortunate to interact closely with top mathematicians and am immersed in an environment with many first-rate mathematicians. The design of the tools will be informed by this experience.

My primary work for a decade or so has been in Automated Theorem Proving, for the last three years with the Lean Prover and LLMs. My work in Lean is at various levels - formalization, programming and (mostly) meta-programming. Meta-programming is where we work with not just a language but with internal representations in the language. Meta-programming in Lean will be a core component of implementation.

## Running the code

The project under development is [open source](https://github.com/siddhartha-gadgil/LeanAide), with instructions to run in the README. Some of it is still very experimental, but feedback is welcome.

## Team

The team that won this award has, besides myself,

* Viraj Kumar, a faculty member at the Kotak Centre in IISc, who will help guide the project.
* Three undergraduates (part-time) interns: Mrigank Pawagi, Anirudh Gupta and Swarnava Chakraborty.
* Shubham Kumar, a software professional who specializes in Function programming and formal verification who will work full-time.

Another full-time postdoc, Ajay Kumar Nair, will be joining the team, as will another part-time intern Malhar Patel.

## Past Contributions

Contributions in the earlier phases are listed in the [README](https://github.com/siddhartha-gadgil/LeanAide/blob/main/README.md) of the project. However, I would like to point to two crucial contributions:

* Anand Rao Tadipatri was an equal contributor with me for the first year or so of this project, before he moved on (to work with Timothy Gowers at Cambridge on related themes).

* I learnt about LLMs and their magic in the pre-ChatGPT era from Naveen Goyal of Microsoft Research, Bangalore. The ML portion was implemented by Ayush Agrawal in the first phase (and to some extent later too).

## The Award and Sponsors

**About the AI for Math Fund**  
The AI for Math Fund seeks to advance the pace and impact of math discovery by supporting projects that are important for the field, but no one academic or industry lab has the incentive to do them. The fund will support projects that (1) are less likely to happen in a business-as-usual scenario; and (2) have the potential to advance the field as a whole. These include: developing open-source, production-quality tools; increasing the size, diversity, and quality of datasets required for training AI models; and increasing the ease-of-use of tools so that they are adopted by mathematicians.

**About Renaissance Philanthropy**  
[Renaissance Philanthropy](https://renaissancephilanthropy.org/) is a nonprofit organization that fuels a 21st-century renaissance by increasing the ambition of philanthropists, scientists and innovators. In the first year, Renaissance Philanthropy catalyzed more than $214M in philanthropic funding for science, technology, and innovation, launching 10+ initiatives across AI, education, climate, health, and scientific infrastructure. The organization designs time-bound, thesis-driven funds led by field experts and inspires talent to take action through playbooks and communities. From accelerating mathematical discovery to expanding talent mobility, Renaissance Philanthropy is building the connective tissue between exceptional ideas and resources to create breakthroughs that transform entire fields.

**About XTX Markets**  
XTX Markets is a leading algorithmic trading firm that uses state-of-the-art machine learning technology to produce price forecasts for over 50,000 financial instruments across equities, fixed income, currencies, commodities, and crypto. It uses those forecasts to trade on exchanges and alternative trading venues, and to offer differentiated liquidity directly to clients worldwide. The firm trades over $250bn a day across 35 countries and has over 250 employees based in London, Singapore, New York, Paris, Bristol, Mumbai and Yerevan.

XTX Markets has an unrivalled level of computational resources in the trading industry, with a growing research cluster currently containing over 25,000 GPUs with 650 petabytes of usable storage. Teams across the firm include world-class researchers with backgrounds in pure math, programming, physics, computer science and machine learning. The firm is also constructing a large-scale data centre in Finland to future-proof its significant computational capabilities.

Since 2020, XTX Markets has committed over £250 million to charities and non-profit partners, establishing the firm as a major philanthropic donor in the UK and globally. The firm’s philanthropy focuses on advancing mathematics education and research, having committed over £50 million in grants to UK charities and education institutions, with the aim of supporting more students to progress to degrees, PhDs, and highly-skilled careers in maths, especially those from low-income backgrounds.
