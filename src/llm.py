import openai
import re
from config import LLMConfig
from abc import ABC, abstractmethod


# Abstract base class defining unified interface
class BaseChatModel(ABC):
    def __init__(self, config: LLMConfig):
        self.config = config
        # Message history for maintaining conversation context
        self.messages = [{"role": "system", "content": "You are a helpful assistant."}]

    @abstractmethod
    def generate_response(self, user_input: str) -> str:
        """
        Generate response based on user input.
        Subclasses must implement this method.
        """
        pass

    def _process_response_think_tags(self, response_text: str) -> str:
        """
        Process <think> tags in response based on configuration.
        """
        if not self.config.think_mode_enabled:
            # If think_mode_enabled is False, remove <think>...</think> parts
            return re.sub(r'<think>.*?</think>', '', response_text, flags=re.DOTALL)
        return response_text


# LLM class using OpenAI-compatible API
class OpenAILLM(BaseChatModel):
    def __init__(self, config: LLMConfig):
        super().__init__(config)
        self.client = openai.OpenAI(
            base_url=self.config.base_url,
            api_key=self.config.api_key
        )
        # Use specific model name and temperature for OpenAI API
        self.model_name = self.config.api_model
        self.temperature = self.config.api_temperature

    def generate_response(self, user_input: str) -> str:
        try:
            # Add user input to message history
            self.messages.append({"role": "user", "content": user_input})

            # Call OpenAI API
            response = self.client.chat.completions.create(
                model=self.model_name,
                messages=self.messages,
                temperature=self.temperature,
            )

            assistant_response = response.choices[0].message.content
            
            # Process <think> tags and update history
            processed_response = self._process_response_think_tags(assistant_response)
            self.messages.append({"role": "assistant", "content": assistant_response})  # Add original response to history to maintain complete context

            return processed_response

        except Exception as e:
            print(f"OpenAI API call failed: {e}")
            # Remove failed user input from history to avoid resending next time
            if self.messages and self.messages[-1]["role"] == "user":
                self.messages.pop()
            return f"Failed to generate response: {e}"


# Main control class that selects LLM implementation based on configuration
class Chatbot:
    def __init__(self, config: LLMConfig):
        self.config = config
        if self.config.use_api_model:
            self.llm_instance = OpenAILLM(config)
        else:
            print("Warning: use_api_model is False, no LLM instance created")
            self.llm_instance = None

    def chat(self, user_input: str) -> str:
        if self.llm_instance is None:
            print("Error: LLM instance is None, cannot generate response")
            return "Error: LLM instance not initialized"
        response = self.llm_instance.generate_response(user_input)
        return response

    def new_chat(self, user_input: str) -> str:
        self.llm_instance = OpenAILLM(self.config)
        response = self.llm_instance.generate_response(user_input)
        return response

