#!/usr/bin/env python3
import os
import sys
import logging
from datetime import datetime
from typing import Optional


class Logger:
    """Logger that outputs to both console and file"""
    
    def __init__(self, log_dir: str, model_name: str, spec_id: int, test_id: int = 1, type_name: str = "lx"):
        self.log_dir = log_dir
        self.model_name = model_name
        self.spec_id = spec_id
        
        # Create log directory
        self.log_path = os.path.join(log_dir, model_name, str(spec_id), str(test_id))
        os.makedirs(self.log_path, exist_ok=True)
        
        # Create log filename (with timestamp)
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_file = os.path.join(self.log_path, f"{timestamp}_{model_name}_{type_name}.log")
        
        # Set log format
        self.log_format = logging.Formatter(
            '%(asctime)s - %(levelname)s - %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S'
        )
        
        # Create logger
        self.logger = logging.getLogger(f"spec_{spec_id}")
        self.logger.setLevel(logging.INFO)
        
        # Clear existing handlers
        self.logger.handlers.clear()
        
        # File handler
        file_handler = logging.FileHandler(self.log_file, encoding='utf-8')
        file_handler.setLevel(logging.INFO)
        file_handler.setFormatter(self.log_format)
        self.logger.addHandler(file_handler)
        
        # Console handler
        console_handler = logging.StreamHandler(sys.stdout)
        console_handler.setLevel(logging.INFO)
        console_handler.setFormatter(self.log_format)
        self.logger.addHandler(console_handler)
        
        # Log start information
        self.logger.info(f"=== Starting processing Spec {spec_id} ===")
        self.logger.info(f"Log file: {self.log_file}")
    
    def info(self, message: str):
        """Log info level message"""
        self.logger.info(message)
    
    def error(self, message: str, exc_info=None):
        """Log error level message
        
        Args:
            message: Error message
            exc_info: If True, include exception info in the log. Can also be an exception tuple.
        """
        if exc_info is not None:
            self.logger.error(message, exc_info=exc_info)
        else:
            self.logger.error(message)
    
    def warning(self, message: str):
        """Log warning level message"""
        self.logger.warning(message)
    
    def debug(self, message: str):
        """Log debug level message"""
        self.logger.debug(message)
    
    def print(self, message: str):
        """Print message to both console and file"""
        self.logger.info(message)
    
    def print_separator(self, char: str = "=", length: int = 50):
        """Print separator line"""
        separator = char * length
        self.logger.info(separator)
    
    def print_section(self, title: str):
        """Print section title"""
        self.print_separator()
        self.logger.info(f"=== {title} ===")
        self.print_separator()
    
    def close(self):
        """Close logger"""
        self.logger.info(f"=== Completed processing Spec {self.spec_id} ===")
        for handler in self.logger.handlers:
            handler.close()
        self.logger.removeHandler(handler)


def get_logger(log_dir: str = None,
               model_name: str = "gpt-4o",
               spec_id: int = 1,
               test_id: int = 1,
               type_name: str = "lx") -> Logger:
    """Get logger instance"""
    if log_dir is None:
        from pathlib import Path
        log_dir = str(Path(__file__).parent.parent / "log")
    return Logger(log_dir, model_name, spec_id, test_id, type_name)

